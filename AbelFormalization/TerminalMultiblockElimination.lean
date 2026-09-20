import AbelFormalization.TerminalLaurentDerivativeExtraction
import AbelFormalization.MultivariateLaurentIdeal
import AbelFormalization.FiniteLaurentLocalization
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Finite multiblock terminal elimination

The simultaneous localized presentation used here has one independent
Laurent exponent for each block and one polynomial variable for each higher
derivative variable.  More precisely, for `h` blocks and `d b` higher
variables in block `b`, it is

`MvPolynomial (Σ b : Fin h, Fin (d b))
  (AddMonoidAlgebra (MvPolynomial Keep R) (Fin h → ℤ))`.

The first variable in block `b` is the standard-basis Laurent monomial.  The
upper-triangular extraction theorem from
`TerminalLaurentDerivativeExtraction` is applied independently to every
`b : Fin h`.  This removes all higher variables.  Closure under the actual
localized multigraded components then makes the resulting Laurent ideal
homogeneous, so `groupAlgebra_homogeneousIdeal_eq_map_comap` removes the
independent Laurent variables as well.
-/

noncomputable section

namespace AbelFormalization

/-! ## A finite-index version of derivative extension -/

/-- The `Fin n` derivative-extension theorem, transported along the chosen
finite equivalence for an arbitrary finite variable type. -/
theorem mvPolynomial_pderiv_stable_ideal_eq_map_comap_fintype
    {C σ : Type*} [CommRing C] [Algebra ℚ C]
    [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ C))
    (hderiv : ∀ i P, P ∈ I → MvPolynomial.pderiv i P ∈ I) :
    I = (I.comap MvPolynomial.C).map MvPolynomial.C := by
  let ε : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let e : MvPolynomial σ C ≃ₐ[C]
      MvPolynomial (Fin (Fintype.card σ)) C :=
    MvPolynomial.renameEquiv C ε
  let J : Ideal (MvPolynomial (Fin (Fintype.card σ)) C) :=
    I.map e.toRingHom
  have hJderiv : ∀ i P, P ∈ J → MvPolynomial.pderiv i P ∈ J := by
    intro i P hP
    have hpre : e.symm P ∈ I := by
      exact (Ideal.symm_apply_mem_of_equiv_iff
        (I := I) (f := e.toRingEquiv) (y := P)).2 hP
    have hd : MvPolynomial.pderiv (ε.symm i) (e.symm P) ∈ I :=
      hderiv (ε.symm i) _ hpre
    have hmap :
        e (MvPolynomial.pderiv (ε.symm i) (e.symm P)) ∈ J := by
      exact (Ideal.apply_mem_of_equiv_iff
        (I := I) (f := e.toRingEquiv)
        (x := MvPolynomial.pderiv (ε.symm i) (e.symm P))).2 hd
    have hintertwine :
        e (MvPolynomial.pderiv (ε.symm i) (e.symm P)) =
          MvPolynomial.pderiv i P := by
      have hr :
          MvPolynomial.pderiv i (e (e.symm P)) =
            e (MvPolynomial.pderiv (ε.symm i) (e.symm P)) := by
        simpa only [e, MvPolynomial.renameEquiv_apply,
          ε.apply_symm_apply] using
            (MvPolynomial.pderiv_rename ε.injective
              (ε.symm i) (e.symm P))
      calc
        e (MvPolynomial.pderiv (ε.symm i) (e.symm P)) =
            MvPolynomial.pderiv i (e (e.symm P)) := hr.symm
        _ = MvPolynomial.pderiv i P := by
          rw [e.apply_symm_apply]
    rw [hintertwine] at hmap
    exact hmap
  have hJ : J = (J.comap MvPolynomial.C).map MvPolynomial.C :=
    mvPolynomial_pderiv_stable_ideal_eq_map_comap
      (Fintype.card σ) J hJderiv
  have hcontraction :
      J.comap MvPolynomial.C = I.comap MvPolynomial.C := by
    ext c
    change MvPolynomial.C c ∈ J ↔ MvPolynomial.C c ∈ I
    have heCsymm :
        e.toRingEquiv.symm (MvPolynomial.C c) = MvPolynomial.C c := by
      simp [e]
    constructor
    · intro hc
      have he := (Ideal.symm_apply_mem_of_equiv_iff
        (I := I) (f := e.toRingEquiv)
        (y := MvPolynomial.C c)).2 hc
      simpa only [heCsymm] using he
    · intro hc
      apply (Ideal.symm_apply_mem_of_equiv_iff
        (I := I) (f := e.toRingEquiv)
        (y := MvPolynomial.C c)).1
      simpa only [heCsymm] using hc
  have heC :
      e.symm.toRingHom.comp
          (MvPolynomial.C : C →+*
            MvPolynomial (Fin (Fintype.card σ)) C) =
        (MvPolynomial.C : C →+* MvPolynomial σ C) := by
    apply RingHom.ext
    intro c
    simp [e]
  calc
    I = J.map e.symm.toRingHom := by
      exact (Ideal.map_of_equiv e.toRingEquiv).symm
    _ = ((J.comap MvPolynomial.C).map MvPolynomial.C).map
          e.symm.toRingHom := by
      exact congrArg (fun L : Ideal
        (MvPolynomial (Fin (Fintype.card σ)) C) =>
          L.map e.symm.toRingHom) hJ
    _ = (J.comap MvPolynomial.C).map
          (e.symm.toRingHom.comp MvPolynomial.C) := by
      rw [Ideal.map_map]
    _ = (J.comap MvPolynomial.C).map MvPolynomial.C := by
      rw [heC]
    _ = (I.comap MvPolynomial.C).map MvPolynomial.C := by
      rw [hcontraction]

/-! ## The simultaneous localized presentation -/

/-- The integer multidegree carried by the independent first variables. -/
abbrev TerminalMultiblockDegree (h : ℕ) := Fin h → ℤ

/-- The dependent finite family of all higher variables.  `⟨b,j⟩`
represents order `j+2` in block `b`. -/
abbrev TerminalMultiblockHigherIndex (h : ℕ) (d : Fin h → ℕ) :=
  Σ b : Fin h, Fin (d b)

/-- The source has one first variable and `d b` higher variables in every
block, followed by the retained variables. -/
abbrev TerminalMultiblockSourceIndex
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) :=
  (Σ b : Fin h, Fin (d b + 1)) ⊕ Keep

abbrev TerminalMultiblockSourceRing
    (R : Type*) [CommRing R] (h : ℕ) (d : Fin h → ℕ)
    (Keep : Type*) :=
  MvPolynomial (TerminalMultiblockSourceIndex h d Keep) R

/-- Retained polynomial coefficients, before adjoining Laurent variables. -/
abbrev TerminalMultiblockRetainedRing
    (R Keep : Type*) [CommRing R] :=
  MvPolynomial Keep R

/-- The independent Laurent first variables over the retained ring. -/
abbrev TerminalMultiblockLaurentRing
    (R Keep : Type*) [CommRing R] (h : ℕ) :=
  AddMonoidAlgebra (TerminalMultiblockRetainedRing R Keep)
    (TerminalMultiblockDegree h)

/-- Higher block variables remain polynomial over the Laurent ring. -/
abbrev TerminalMultiblockLocalizedRing
    (R Keep : Type*) [CommRing R] (h : ℕ) (d : Fin h → ℕ) :=
  MvPolynomial (TerminalMultiblockHigherIndex h d)
    (TerminalMultiblockLaurentRing R Keep h)

section Presentation

variable (R Keep : Type*) [CommRing R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- The standard exponent of the first variable in block `b`. -/
def terminalMultiblockFirstExponent (b : Fin h) :
    TerminalMultiblockDegree h :=
  finiteLaurentExponentHom h (Finsupp.single b 1)

@[simp]
theorem terminalMultiblockFirstExponent_apply
    (b c : Fin h) :
    terminalMultiblockFirstExponent h b c = if b = c then 1 else 0 := by
  classical
  simp [terminalMultiblockFirstExponent, finiteLaurentExponentHom_apply,
    Finsupp.single_apply]

/-- The standard group monomial representing the first variable in block
`b`, included as a constant in the higher-variable polynomial ring. -/
def terminalMultiblockFirstVariable (b : Fin h) :
    TerminalMultiblockLocalizedRing R Keep h d :=
  MvPolynomial.C
    (AddMonoidAlgebra.single (terminalMultiblockFirstExponent h b) 1)

/-- Every block's first variable is a unit in the simultaneous localized
presentation. -/
theorem terminalMultiblockFirstVariable_isUnit (b : Fin h) :
    IsUnit (terminalMultiblockFirstVariable R Keep h d b) := by
  simpa only [terminalMultiblockFirstVariable] using
    (finiteLaurent_single_isUnit
      (TerminalMultiblockRetainedRing R Keep) h
      (terminalMultiblockFirstExponent h b)).map
        (MvPolynomial.C :
          TerminalMultiblockLaurentRing R Keep h →+*
            TerminalMultiblockLocalizedRing R Keep h d)

/-- The image of a source block variable. -/
def terminalMultiblockBlockVariable (b : Fin h) :
    Fin (d b + 1) → TerminalMultiblockLocalizedRing R Keep h d :=
  Fin.cases (terminalMultiblockFirstVariable R Keep h d b)
    (fun j ↦ MvPolynomial.X ⟨b, j⟩)

@[simp]
theorem terminalMultiblockBlockVariable_zero (b : Fin h) :
    terminalMultiblockBlockVariable R Keep h d b 0 =
      terminalMultiblockFirstVariable R Keep h d b :=
  rfl

@[simp]
theorem terminalMultiblockBlockVariable_succ
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockBlockVariable R Keep h d b j.succ =
      MvPolynomial.X ⟨b, j⟩ :=
  rfl

/-- Original scalar coefficients land in Laurent degree zero and polynomial
degree zero. -/
def terminalMultiblockBaseMap :
    R →+* TerminalMultiblockLocalizedRing R Keep h d :=
  (MvPolynomial.C :
      TerminalMultiblockLaurentRing R Keep h →+*
        TerminalMultiblockLocalizedRing R Keep h d).comp
    ((groupAlgebraC
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockDegree h)).comp
        (MvPolynomial.C : R →+* TerminalMultiblockRetainedRing R Keep))

/-- Images of source variables in the simultaneous localization. -/
def terminalMultiblockVariableImage :
    TerminalMultiblockSourceIndex h d Keep →
      TerminalMultiblockLocalizedRing R Keep h d
  | Sum.inl ⟨b, r⟩ => terminalMultiblockBlockVariable R Keep h d b r
  | Sum.inr k =>
      MvPolynomial.C
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h) (MvPolynomial.X k))

/-- The simultaneous original-to-localized ring homomorphism. -/
def terminalMultiblockLocalizationHom :
    TerminalMultiblockSourceRing R h d Keep →+*
      TerminalMultiblockLocalizedRing R Keep h d :=
  MvPolynomial.eval₂Hom (terminalMultiblockBaseMap R Keep h d)
    (terminalMultiblockVariableImage R Keep h d)

@[simp]
theorem terminalMultiblockLocalizationHom_C (a : R) :
    terminalMultiblockLocalizationHom R Keep h d (MvPolynomial.C a) =
      MvPolynomial.C
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h) (MvPolynomial.C a)) := by
  simp [terminalMultiblockLocalizationHom, terminalMultiblockBaseMap]

@[simp]
theorem terminalMultiblockLocalizationHom_X_keep (k : Keep) :
    terminalMultiblockLocalizationHom R Keep h d
        (MvPolynomial.X (Sum.inr k)) =
      MvPolynomial.C
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h) (MvPolynomial.X k)) := by
  simp [terminalMultiblockLocalizationHom, terminalMultiblockVariableImage]

@[simp]
theorem terminalMultiblockLocalizationHom_X_first (b : Fin h) :
    terminalMultiblockLocalizationHom R Keep h d
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩)) =
      terminalMultiblockFirstVariable R Keep h d b := by
  simp [terminalMultiblockLocalizationHom, terminalMultiblockVariableImage]

@[simp]
theorem terminalMultiblockLocalizationHom_X_higher
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockLocalizationHom R Keep h d
        (MvPolynomial.X (Sum.inl ⟨b, j.succ⟩)) =
      MvPolynomial.X ⟨b, j⟩ := by
  simp [terminalMultiblockLocalizationHom, terminalMultiblockVariableImage]

/-- Commuting the two additive-monoid-algebra layers identifies the chosen
presentation with Laurent polynomials whose coefficients are polynomials in
the retained and higher variables. -/
def terminalMultiblockPolynomialLaurentEquiv :
    TerminalMultiblockLocalizedRing R Keep h d ≃ₐ[
      TerminalMultiblockRetainedRing R Keep]
      AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h) :=
  AddMonoidAlgebra.commAlgEquiv (TerminalMultiblockRetainedRing R Keep)

end Presentation

/-! ## Blockwise upper-triangular extraction -/

section BlockwiseExtraction

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- Partial derivative with respect to the higher variable `⟨b,j⟩`,
viewed over `ℚ`. -/
def terminalMultiblockHigherPDeriv (b : Fin h) (j : Fin (d b)) :
    Derivation ℚ (TerminalMultiblockLocalizedRing R Keep h d)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
  (MvPolynomial.pderiv (⟨b, j⟩ : TerminalMultiblockHigherIndex h d) :
      Derivation (TerminalMultiblockLaurentRing R Keep h)
        (TerminalMultiblockLocalizedRing R Keep h d)
        (TerminalMultiblockLocalizedRing R Keep h d)).restrictScalars ℚ

/-- Strict upper-triangular coefficient inside one block. -/
def terminalMultiblockOffDiagonalCoefficient
    (b : Fin h) (j k : Fin (d b)) :
    TerminalMultiblockLocalizedRing R Keep h d :=
  if hjk : j < k then
    ((k.val + 2).choose (j.val + 2) :
        TerminalMultiblockLocalizedRing R Keep h d) *
      MvPolynomial.X
        ⟨b, terminalLaurentHigherIndex (d b) j k hjk⟩
  else 0

/-- The localized `V_(j+1)` field in block `b`, in its exact triangular
form. -/
def terminalMultiblockTriangularField
    (b : Fin h) (j : Fin (d b)) :
    Derivation ℚ (TerminalMultiblockLocalizedRing R Keep h d)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
  terminalMultiblockFirstVariable R Keep h d b •
      terminalMultiblockHigherPDeriv R Keep h d b j +
    ∑ k ∈ Finset.Ioi j,
      terminalMultiblockOffDiagonalCoefficient R Keep h d b j k •
        terminalMultiblockHigherPDeriv R Keep h d b k

theorem terminalMultiblockTriangularField_eq
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockTriangularField R Keep h d b j =
      terminalMultiblockFirstVariable R Keep h d b •
          terminalMultiblockHigherPDeriv R Keep h d b j +
        ∑ k ∈ Finset.Ioi j,
          terminalMultiblockOffDiagonalCoefficient R Keep h d b j k •
            terminalMultiblockHigherPDeriv R Keep h d b k :=
  rfl

/-- Exact intertwining of source block fields with the displayed localized
triangular fields transports preservation to the simultaneously mapped
ideal.  This is the interface used by the global terminal-field calculation:
that calculation only has to establish the generator identities and then
the resulting equality of derivations. -/
theorem terminalMultiblockTriangularField_preserves_mappedIdeal
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (V : ∀ b : Fin h, Fin (d b) →
      Derivation ℚ (TerminalMultiblockSourceRing R h d Keep)
        (TerminalMultiblockSourceRing R h d Keep))
    (hV : ∀ b j, derivationPreservesIdeal I (V b j))
    (hintertwine : ∀ b j P,
      terminalMultiblockLocalizationHom R Keep h d (V b j P) =
        terminalMultiblockTriangularField R Keep h d b j
          (terminalMultiblockLocalizationHom R Keep h d P)) :
    ∀ (b : Fin h) (j : Fin (d b)), derivationPreservesIdeal
      (A := TerminalMultiblockLocalizedRing R Keep h d)
      (I.map (terminalMultiblockLocalizationHom R Keep h d))
      (terminalMultiblockTriangularField R Keep h d b j) := by
  intro b j
  apply derivationPreservesIdeal_map_of_intertwining
    (A := TerminalMultiblockSourceRing R h d Keep)
    (B := TerminalMultiblockLocalizedRing R Keep h d)
    (terminalMultiblockLocalizationHom R Keep h d) I
    (V b j) (terminalMultiblockTriangularField R Keep h d b j)
  · exact hintertwine b j
  · exact hV b j

/-- Applying the one-block unit-triangular extractor separately in every
finite block gives stability under all higher-variable partial derivatives. -/
theorem terminalMultiblock_pderiv_stable_of_triangular
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hfield : ∀ (b : Fin h) (j : Fin (d b)),
      derivationPreservesIdeal
        (A := TerminalMultiblockLocalizedRing R Keep h d) K
        (terminalMultiblockTriangularField R Keep h d b j)) :
    ∀ x P, P ∈ K → MvPolynomial.pderiv x P ∈ K := by
  rintro ⟨b, j⟩ P hP
  have hblock : ∀ k : Fin (d b),
      derivationPreservesIdeal
        (A := TerminalMultiblockLocalizedRing R Keep h d) K
        (terminalMultiblockHigherPDeriv R Keep h d b k) := by
    apply derivationPreservesIdeal_of_unit_upperTriangular
      K (terminalMultiblockFirstVariable R Keep h d b)
      (terminalMultiblockFirstVariable_isUnit R Keep h d b)
      (terminalMultiblockHigherPDeriv R Keep h d b)
      (terminalMultiblockTriangularField R Keep h d b)
      (terminalMultiblockOffDiagonalCoefficient R Keep h d b)
    · exact hfield b
    · exact terminalMultiblockTriangularField_eq R Keep h d b
  simpa only [terminalMultiblockHigherPDeriv,
    Derivation.restrictScalars_apply] using hblock j P hP

/-- Iterating the one-block extraction over `Fin h` eliminates all higher
variables from the localized ideal. -/
theorem terminalMultiblockHigherElimination
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hfield : ∀ (b : Fin h) (j : Fin (d b)),
      derivationPreservesIdeal
        (A := TerminalMultiblockLocalizedRing R Keep h d) K
        (terminalMultiblockTriangularField R Keep h d b j)) :
    K = (K.comap MvPolynomial.C).map MvPolynomial.C := by
  classical
  exact mvPolynomial_pderiv_stable_ideal_eq_map_comap_fintype K
    (terminalMultiblock_pderiv_stable_of_triangular R Keep h d K hfield)

/-- Source preservation plus the exact localized field identities eliminate
all higher variables from the mapped ideal. -/
theorem terminalMultiblockMappedIdealHigherElimination
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (V : ∀ b : Fin h, Fin (d b) →
      Derivation ℚ (TerminalMultiblockSourceRing R h d Keep)
        (TerminalMultiblockSourceRing R h d Keep))
    (hV : ∀ b j, derivationPreservesIdeal I (V b j))
    (hintertwine : ∀ b j P,
      terminalMultiblockLocalizationHom R Keep h d (V b j P) =
        terminalMultiblockTriangularField R Keep h d b j
          (terminalMultiblockLocalizationHom R Keep h d P)) :
    I.map (terminalMultiblockLocalizationHom R Keep h d) =
      ((I.map (terminalMultiblockLocalizationHom R Keep h d)).comap
        MvPolynomial.C).map MvPolynomial.C := by
  apply terminalMultiblockHigherElimination R Keep h d
  exact terminalMultiblockTriangularField_preserves_mappedIdeal
    R Keep h d I V hV hintertwine

end BlockwiseExtraction

/-! ## The multigraded Laurent contraction -/

section Multigrading

variable (R Keep : Type*) [CommRing R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- A higher variable of order `j+2` has `(j+2)e_b` as its multidegree. -/
def terminalMultiblockHigherWeight
    (x : TerminalMultiblockHigherIndex h d) :
    TerminalMultiblockDegree h :=
  (x.2.val + 2) • terminalMultiblockFirstExponent h x.1

/-- Projection to one total multidegree in the polynomial-over-Laurent
presentation.  For a polynomial monomial `m`, it selects Laurent coefficient
degree `α - weight(m)`. -/
def terminalMultiblockLocalizedComponent
    (degree : TerminalMultiblockDegree h)
    (P : TerminalMultiblockLocalizedRing R Keep h d) :
    TerminalMultiblockLocalizedRing R Keep h d :=
  ∑ m ∈ P.support,
    MvPolynomial.monomial m
      (AddMonoidAlgebra.single
        (degree - Finsupp.weight (terminalMultiblockHigherWeight h d) m)
        ((P.coeff m).coeff
          (degree - Finsupp.weight
            (terminalMultiblockHigherWeight h d) m)))

/-- Closure under the actual total multigraded projections in the localized
presentation. -/
def IsTerminalMultiblockLocalizedMultigraded
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d)) : Prop :=
  ∀ P ∈ K, ∀ degree,
    terminalMultiblockLocalizedComponent R Keep h d degree P ∈ K

/-- On a constant higher-variable polynomial, the localized component is
exactly the identity-grading component of its Laurent coefficient. -/
@[simp]
theorem terminalMultiblockLocalizedComponent_C
    (degree : TerminalMultiblockDegree h)
    (f : TerminalMultiblockLaurentRing R Keep h) :
    terminalMultiblockLocalizedComponent R Keep h d degree
        (MvPolynomial.C f) =
      MvPolynomial.C (AddMonoidAlgebra.single degree (f.coeff degree)) := by
  classical
  by_cases hf : f = 0
  · subst f
    simp [terminalMultiblockLocalizedComponent]
  · simp [terminalMultiblockLocalizedComponent,
      MvPolynomial.support_C, hf]

/-- Closure under all single coefficient components characterizes enough
homogeneity for the additive-group-algebra extension theorem. -/
theorem groupAlgebra_isHomogeneous_of_single_coeff_mem
    {C G : Type*} [CommRing C] [AddCommGroup G] [DecidableEq G]
    (J : Ideal (AddMonoidAlgebra C G))
    (hcomponent : ∀ f ∈ J, ∀ g,
      AddMonoidAlgebra.single g (f.coeff g) ∈ J) :
    J.IsHomogeneous (AddMonoidAlgebra.grade C) := by
  let S : Set (SetLike.homogeneousSubmonoid
      (AddMonoidAlgebra.grade C)) :=
    {f | f.1 ∈ J}
  apply (Ideal.IsHomogeneous.iff_exists
    (AddMonoidAlgebra.grade C) J).2
  refine ⟨S, le_antisymm ?_ ?_⟩
  · intro f hf
    rw [← AddMonoidAlgebra.sum_coeff_single f]
    apply Ideal.sum_mem
    intro g hg
    apply Ideal.subset_span
    refine ⟨⟨AddMonoidAlgebra.single g (f.coeff g), ?_⟩, ?_, rfl⟩
    · exact ⟨g, AddMonoidAlgebra.single_mem_grade g (f.coeff g)⟩
    · exact hcomponent f hf g
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact hf

/-- The higher-variable contraction is closed under every Laurent
single-degree projection.  This is the concrete multigraded statement used
to manufacture the abstract `Ideal.IsHomogeneous` witness below. -/
theorem terminalMultiblockHigherContraction_component_mem
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hgraded : IsTerminalMultiblockLocalizedMultigraded R Keep h d K)
    (f : TerminalMultiblockLaurentRing R Keep h)
    (hf : f ∈ K.comap MvPolynomial.C)
    (degree : TerminalMultiblockDegree h) :
    AddMonoidAlgebra.single degree (f.coeff degree) ∈
      K.comap MvPolynomial.C := by
  change MvPolynomial.C f ∈ K at hf
  change MvPolynomial.C
    (AddMonoidAlgebra.single degree (f.coeff degree)) ∈ K
  rw [← terminalMultiblockLocalizedComponent_C R Keep h d degree f]
  exact hgraded (MvPolynomial.C f) hf degree

/-- The contraction obtained after removing the higher variables remains
multigraded for the identity grading on the independent Laurent exponents. -/
theorem terminalMultiblockHigherContraction_isHomogeneous
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hgraded : IsTerminalMultiblockLocalizedMultigraded R Keep h d K) :
    (K.comap MvPolynomial.C).IsHomogeneous
      (AddMonoidAlgebra.grade
        (TerminalMultiblockRetainedRing R Keep)) := by
  classical
  apply groupAlgebra_isHomogeneous_of_single_coeff_mem
  intro f hf degree
  exact terminalMultiblockHigherContraction_component_mem
    R Keep h d K hgraded f hf degree

/-- The retained coefficient contraction after first removing higher
variables and then the Laurent first variables. -/
def terminalMultiblockRetainedContraction
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d)) :
    Ideal (TerminalMultiblockRetainedRing R Keep) :=
  (K.comap MvPolynomial.C).comap
    (groupAlgebraC
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockDegree h))

/-- Direct inclusion of retained coefficients into the simultaneous
localized presentation. -/
def terminalMultiblockRetainedCoefficientHom :
    TerminalMultiblockRetainedRing R Keep →+*
      TerminalMultiblockLocalizedRing R Keep h d :=
  (MvPolynomial.C :
      TerminalMultiblockLaurentRing R Keep h →+*
        TerminalMultiblockLocalizedRing R Keep h d).comp
    (groupAlgebraC
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockDegree h))

/-- Once the higher-variable contraction is homogeneous, the remaining
Laurent ideal is extended from precisely the retained coefficients. -/
theorem terminalMultiblockHigherContraction_eq_map_retained_of_isHomogeneous
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hhomogeneous : (K.comap MvPolynomial.C).IsHomogeneous
      (AddMonoidAlgebra.grade
        (TerminalMultiblockRetainedRing R Keep))) :
    K.comap MvPolynomial.C =
      (terminalMultiblockRetainedContraction R Keep h d K).map
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h)) := by
  classical
  exact groupAlgebra_homogeneousIdeal_eq_map_comap _ hhomogeneous

/-- Concrete localized component closure supplies the abstract homogeneity
input required by the additive-group-algebra extension theorem. -/
theorem terminalMultiblockHigherContraction_eq_map_retained
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hgraded : IsTerminalMultiblockLocalizedMultigraded R Keep h d K) :
    K.comap MvPolynomial.C =
      (terminalMultiblockRetainedContraction R Keep h d K).map
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h)) := by
  exact
    terminalMultiblockHigherContraction_eq_map_retained_of_isHomogeneous
      R Keep h d K
        (terminalMultiblockHigherContraction_isHomogeneous
          R Keep h d K hgraded)

end Multigrading

/-! ## Complete multiblock elimination -/

section Final

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- Abstract-homogeneity form of finite multiblock elimination.  This is
useful when the preceding geometric argument already constructs an
`Ideal.IsHomogeneous` witness for the Laurent contraction. -/
theorem terminalMultiblockElimination_of_isHomogeneous
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hfield : ∀ (b : Fin h) (j : Fin (d b)),
      derivationPreservesIdeal
        (A := TerminalMultiblockLocalizedRing R Keep h d) K
        (terminalMultiblockTriangularField R Keep h d b j))
    (hhomogeneous : (K.comap MvPolynomial.C).IsHomogeneous
      (AddMonoidAlgebra.grade
        (TerminalMultiblockRetainedRing R Keep))) :
    K = (terminalMultiblockRetainedContraction R Keep h d K).map
      (terminalMultiblockRetainedCoefficientHom R Keep h d) := by
  have hhigher : K = (K.comap MvPolynomial.C).map MvPolynomial.C :=
    terminalMultiblockHigherElimination R Keep h d K hfield
  have hlaurent : K.comap MvPolynomial.C =
      (terminalMultiblockRetainedContraction R Keep h d K).map
        (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h)) :=
    terminalMultiblockHigherContraction_eq_map_retained_of_isHomogeneous
      R Keep h d K hhomogeneous
  calc
    K = (K.comap MvPolynomial.C).map MvPolynomial.C := hhigher
    _ = ((terminalMultiblockRetainedContraction R Keep h d K).map
          (groupAlgebraC
            (TerminalMultiblockRetainedRing R Keep)
            (TerminalMultiblockDegree h))).map MvPolynomial.C := by
      rw [hlaurent]
    _ = (terminalMultiblockRetainedContraction R Keep h d K).map
          (terminalMultiblockRetainedCoefficientHom R Keep h d) := by
      rw [Ideal.map_map]
      rfl

/-- The exact finite multiblock terminal conclusion.  Blockwise preservation
of the localized triangular fields removes every higher variable; localized
multigraded closure then removes every independent Laurent first variable. -/
theorem terminalMultiblockElimination
    (K : Ideal (TerminalMultiblockLocalizedRing R Keep h d))
    (hfield : ∀ (b : Fin h) (j : Fin (d b)),
      derivationPreservesIdeal
        (A := TerminalMultiblockLocalizedRing R Keep h d) K
        (terminalMultiblockTriangularField R Keep h d b j))
    (hgraded : IsTerminalMultiblockLocalizedMultigraded R Keep h d K) :
    K = (terminalMultiblockRetainedContraction R Keep h d K).map
      (terminalMultiblockRetainedCoefficientHom R Keep h d) := by
  apply terminalMultiblockElimination_of_isHomogeneous R Keep h d K hfield
  exact terminalMultiblockHigherContraction_isHomogeneous
    R Keep h d K hgraded

/-- End-to-end mapped-ideal form.  The two inputs expected from the terminal
geometry are exactly: the source invariant fields preserve `I` and, after
the simultaneous localization, those fields have the displayed blockwise
triangular form.  The remaining input records preservation of the genuine
total multidegree components under the same localization. -/
theorem terminalMultiblockMappedIdealElimination
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (V : ∀ b : Fin h, Fin (d b) →
      Derivation ℚ (TerminalMultiblockSourceRing R h d Keep)
        (TerminalMultiblockSourceRing R h d Keep))
    (hV : ∀ b j, derivationPreservesIdeal I (V b j))
    (hintertwine : ∀ b j P,
      terminalMultiblockLocalizationHom R Keep h d (V b j P) =
        terminalMultiblockTriangularField R Keep h d b j
          (terminalMultiblockLocalizationHom R Keep h d P))
    (hgraded : IsTerminalMultiblockLocalizedMultigraded R Keep h d
      (I.map (terminalMultiblockLocalizationHom R Keep h d))) :
    I.map (terminalMultiblockLocalizationHom R Keep h d) =
      (terminalMultiblockRetainedContraction R Keep h d
        (I.map (terminalMultiblockLocalizationHom R Keep h d))).map
          (terminalMultiblockRetainedCoefficientHom R Keep h d) := by
  apply terminalMultiblockElimination R Keep h d
  · exact terminalMultiblockTriangularField_preserves_mappedIdeal
      R Keep h d I V hV hintertwine
  · exact hgraded

end Final

end AbelFormalization
