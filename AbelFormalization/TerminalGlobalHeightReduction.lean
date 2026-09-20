import AbelFormalization.TerminalGlobalAlgebraicElimination
import AbelFormalization.CentralLaurentLocalization

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option diagnostics false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Height after terminal algebraic elimination

The simultaneous terminal localization is, up to explicit polynomial and
Laurent ring equivalences, the ordinary localization which inverts one
variable in each terminal block.  It therefore cannot lower ideal height.
Coefficient extension from the retained polynomial ring preserves height,
so the terminal elimination identity gives the manuscript's retained-height
inequality.
-/

noncomputable section

namespace AbelFormalization

/-- Use the semiring reduct of the canonical commutative-ring structure so
ideal heights and the polynomial presentation share one typeclass path. -/
local instance (priority := 2000) terminalMultiblockLocalizedSemiring
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    Semiring (TerminalMultiblockLocalizedRing R Keep h d) :=
  (inferInstance : CommRing
    (TerminalMultiblockLocalizedRing R Keep h d)).toSemiring

/-- Split every terminal block into its first variable and its higher
variables. -/
def terminalMultiblockBlockSplitEquiv
    (h : ℕ) (d : Fin h → ℕ) :
    (Σ b : Fin h, Fin (d b + 1)) ≃
      Fin h ⊕ TerminalMultiblockHigherIndex h d where
  toFun x := Fin.cases (Sum.inl x.1) (fun j ↦ Sum.inr ⟨x.1, j⟩) x.2
  invFun
    | Sum.inl b => ⟨b, 0⟩
    | Sum.inr x => ⟨x.1, x.2.succ⟩
  left_inv := by
    rintro ⟨b, r⟩
    exact Fin.cases rfl (fun _ ↦ rfl) r
  right_inv := by
    rintro (b | ⟨b, j⟩) <;> rfl

/-- Group the split block variables before the retained variables. -/
def terminalMultiblockSourceGroupedIndexEquiv
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) :
    TerminalMultiblockSourceIndex h d Keep ≃
      (Fin h ⊕ TerminalMultiblockHigherIndex h d) ⊕ Keep :=
  Equiv.sumCongr (terminalMultiblockBlockSplitEquiv h d) (Equiv.refl Keep)

/-- Present the source as a polynomial ring in first and higher block
variables over the retained polynomial coefficient ring. -/
def terminalMultiblockCentralSourceEquiv
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    TerminalMultiblockSourceRing R h d Keep ≃ₐ[R]
      MvPolynomial (Fin h ⊕ TerminalMultiblockHigherIndex h d)
        (TerminalMultiblockRetainedRing R Keep) :=
  (MvPolynomial.renameEquiv R
    (terminalMultiblockSourceGroupedIndexEquiv h d Keep)).trans
      (MvPolynomial.sumAlgEquiv R
        (Fin h ⊕ TerminalMultiblockHigherIndex h d) Keep)

@[simp]
theorem terminalMultiblockSourceGroupedIndexEquiv_first
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) (b : Fin h) :
    terminalMultiblockSourceGroupedIndexEquiv h d Keep
        (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩) = Sum.inl (Sum.inl b) :=
  rfl

@[simp]
theorem terminalMultiblockSourceGroupedIndexEquiv_higher
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*)
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockSourceGroupedIndexEquiv h d Keep
        (Sum.inl ⟨b, j.succ⟩) = Sum.inl (Sum.inr ⟨b, j⟩) :=
  rfl

@[simp]
theorem terminalMultiblockSourceGroupedIndexEquiv_keep
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) (k : Keep) :
    terminalMultiblockSourceGroupedIndexEquiv h d Keep (Sum.inr k) =
      Sum.inr k :=
  rfl

/-- Under the two explicit presentation equivalences, simultaneous terminal
localization is the standard finite Laurent-polynomial inclusion. -/
theorem terminalMultiblockLocalizationHom_equiv
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    (terminalMultiblockPolynomialLaurentEquiv R Keep h d).toRingEquiv.toRingHom.comp
        (terminalMultiblockLocalizationHom R Keep h d) =
      (centralLaurentPolynomialMap
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockHigherIndex h d) h).comp
        (terminalMultiblockCentralSourceEquiv R Keep h d).toRingEquiv.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [terminalMultiblockPolynomialLaurentEquiv,
      terminalMultiblockCentralSourceEquiv, centralLaurentPolynomialMap]
    simp only [MvPolynomial.C_apply,
      ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.commAlgEquiv_single_single]
  · rintro (⟨b, r⟩ | k)
    · refine Fin.cases ?_ (fun j ↦ ?_) r
      · simp [terminalMultiblockPolynomialLaurentEquiv,
          terminalMultiblockCentralSourceEquiv, centralLaurentPolynomialMap,
          terminalMultiblockFirstVariable]
        simp only [MvPolynomial.C_apply,
          ← MvPolynomial.single_eq_monomial,
          AddMonoidAlgebra.commAlgEquiv_single_single]
        simp [terminalMultiblockFirstExponent, AddMonoidAlgebra.one_def]
      · simp [terminalMultiblockPolynomialLaurentEquiv,
          terminalMultiblockCentralSourceEquiv, centralLaurentPolynomialMap]
        simp only [MvPolynomial.X,
          ← MvPolynomial.single_eq_monomial,
          AddMonoidAlgebra.commAlgEquiv_single_zero]
    · simp [terminalMultiblockPolynomialLaurentEquiv,
        terminalMultiblockCentralSourceEquiv, centralLaurentPolynomialMap]
      simp only [MvPolynomial.C_apply,
        ← MvPolynomial.single_eq_monomial,
        AddMonoidAlgebra.commAlgEquiv_single_single]

/-- The source regrouping equivalence preserves height. -/
theorem terminalMultiblockCentralSourceEquiv_height_map
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ)
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep)) :
    (I.map (terminalMultiblockCentralSourceEquiv
      R Keep h d).toRingEquiv.toRingHom).height = I.height :=
  (terminalMultiblockCentralSourceEquiv
    R Keep h d).toRingEquiv.height_map I

/-- The two equivalent presentations give exactly the same mapped ideal. -/
theorem terminalMultiblockLocalizationHom_map_equiv
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ)
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep)) :
    (I.map (terminalMultiblockLocalizationHom R Keep h d)).map
        (terminalMultiblockPolynomialLaurentEquiv
          R Keep h d).toRingEquiv.toRingHom =
      (I.map (terminalMultiblockCentralSourceEquiv
        R Keep h d).toRingEquiv.toRingHom).map
        (centralLaurentPolynomialMap
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockHigherIndex h d) h) := by
  rw [Ideal.map_map, Ideal.map_map,
    terminalMultiblockLocalizationHom_equiv]

/-- Use the literal central Laurent map as its algebra structure map. -/
local instance terminalCentralLaurentPolynomialAlgebra
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    Algebra
      (MvPolynomial (Fin h ⊕ TerminalMultiblockHigherIndex h d)
        (TerminalMultiblockRetainedRing R Keep))
      (AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h)) :=
  (centralLaurentPolynomialMap
    (TerminalMultiblockRetainedRing R Keep)
    (TerminalMultiblockHigherIndex h d) h).toAlgebra

/-- Use simultaneous terminal localization as the source algebra map. -/
local instance terminalMultiblockLocalizationAlgebra
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    Algebra (TerminalMultiblockSourceRing R h d Keep)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
  (terminalMultiblockLocalizationHom R Keep h d).toAlgebra

/-- The standard central Laurent target, regarded as an algebra over the
original terminal source through the source regrouping equivalence. -/
local instance terminalMultiblockCentralTargetAlgebra
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    Algebra (TerminalMultiblockSourceRing R h d Keep)
      (AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h)) :=
  ((centralLaurentPolynomialMap
    (TerminalMultiblockRetainedRing R Keep)
    (TerminalMultiblockHigherIndex h d) h).comp
      (terminalMultiblockCentralSourceEquiv
        R Keep h d).toRingEquiv.toRingHom).toAlgebra

/-- The multiplicative set inverted by simultaneous terminal localization. -/
def terminalMultiblockLocalizationSubmonoid
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    Submonoid (TerminalMultiblockSourceRing R h d Keep) :=
  (centralLaurentVariableSubmonoid
    (TerminalMultiblockRetainedRing R Keep)
    (TerminalMultiblockHigherIndex h d) h).comap
      (terminalMultiblockCentralSourceEquiv
        R Keep h d).toRingEquiv.toMonoidHom

/-- Before commuting the polynomial and Laurent layers, the central target is
already the required localization of the original terminal source. -/
theorem terminalMultiblockCentralTarget_isLocalization
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    IsLocalization (terminalMultiblockLocalizationSubmonoid R Keep h d)
      (AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h)) := by
  letI : IsLocalization
      (centralLaurentVariableSubmonoid
        (TerminalMultiblockRetainedRing R Keep)
        (TerminalMultiblockHigherIndex h d) h)
      (AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h)) :=
    centralLaurentPolynomial_isLocalization
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockHigherIndex h d) h
  apply IsLocalization.of_ringEquiv_left
    (R := TerminalMultiblockSourceRing R h d Keep)
    (S := MvPolynomial (Fin h ⊕ TerminalMultiblockHigherIndex h d)
      (TerminalMultiblockRetainedRing R Keep))
    (K := AddMonoidAlgebra
      (MvPolynomial (TerminalMultiblockHigherIndex h d)
        (TerminalMultiblockRetainedRing R Keep))
      (TerminalMultiblockDegree h))
    (M₁ := centralLaurentVariableSubmonoid
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockHigherIndex h d) h)
    (M₂ := terminalMultiblockLocalizationSubmonoid R Keep h d)
    (terminalMultiblockCentralSourceEquiv R Keep h d).toRingEquiv
  · exact Submonoid.map_comap_eq_of_surjective
      (terminalMultiblockCentralSourceEquiv R Keep h d).surjective _
  · intro x
    rfl

/-- Commute the standard central localization back to the terminal localized
presentation, as an equivalence over the original source ring. -/
def terminalMultiblockCentralTargetAlgEquiv
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    AddMonoidAlgebra
      (MvPolynomial (TerminalMultiblockHigherIndex h d)
        (TerminalMultiblockRetainedRing R Keep))
      (TerminalMultiblockDegree h) ≃ₐ[
        TerminalMultiblockSourceRing R h d Keep]
      TerminalMultiblockLocalizedRing R Keep h d := by
  apply AlgEquiv.ofRingEquiv
    (f := (terminalMultiblockPolynomialLaurentEquiv
      R Keep h d).symm.toRingEquiv)
  intro x
  have hx := DFunLike.congr_fun
    (terminalMultiblockLocalizationHom_equiv R Keep h d) x
  apply (terminalMultiblockPolynomialLaurentEquiv
    R Keep h d).symm_apply_eq.mpr
  simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
    algEquiv_toRingEquiv_toRingHom_apply] using hx.symm

/-- The simultaneous terminal presentation is the localization of the source
at the displayed multiplicative set. -/
theorem terminalMultiblock_isLocalization
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    IsLocalization (terminalMultiblockLocalizationSubmonoid R Keep h d)
      (TerminalMultiblockLocalizedRing R Keep h d) := by
  letI : IsLocalization
      (terminalMultiblockLocalizationSubmonoid R Keep h d)
      (AddMonoidAlgebra
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep))
        (TerminalMultiblockDegree h)) :=
    terminalMultiblockCentralTarget_isLocalization R Keep h d
  exact IsLocalization.isLocalization_of_algEquiv
    (terminalMultiblockLocalizationSubmonoid R Keep h d)
    (terminalMultiblockCentralTargetAlgEquiv R Keep h d)

/-- Simultaneously inverting the first variable of every terminal block
cannot lower ideal height. -/
theorem terminalMultiblockLocalizationHom_height_le
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ)
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep)) :
    I.height ≤
      (I.map (terminalMultiblockLocalizationHom R Keep h d)).height := by
  letI : IsLocalization
      (terminalMultiblockLocalizationSubmonoid R Keep h d)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
    terminalMultiblock_isLocalization R Keep h d
  change I.height ≤
    (I.map (algebraMap
      (TerminalMultiblockSourceRing R h d Keep)
      (TerminalMultiblockLocalizedRing R Keep h d))).height
  calc
    I.height ≤ (((I.map (algebraMap
        (TerminalMultiblockSourceRing R h d Keep)
        (TerminalMultiblockLocalizedRing R Keep h d))).comap
          (algebraMap
            (TerminalMultiblockSourceRing R h d Keep)
            (TerminalMultiblockLocalizedRing R Keep h d)))).height :=
      Ideal.height_mono Ideal.le_comap_map
    _ = (I.map (algebraMap
          (TerminalMultiblockSourceRing R h d Keep)
          (TerminalMultiblockLocalizedRing R Keep h d))).height :=
      idealHeight_localization_under
        (terminalMultiblockLocalizationSubmonoid R Keep h d) _

/-- Extending an ideal of the retained polynomial ring through all Laurent
first variables and higher polynomial variables preserves height. -/
theorem terminalMultiblockRetainedCoefficientHom_height_map
    (R Keep : Type*) [CommRing R] [IsNoetherianRing R] [Finite Keep]
    (h : ℕ) (d : Fin h → ℕ)
    (C : Ideal (TerminalMultiblockRetainedRing R Keep)) :
    (C.map (terminalMultiblockRetainedCoefficientHom R Keep h d)).height =
      C.height := by
  letI : IsNoetherianRing (TerminalMultiblockRetainedRing R Keep) :=
    inferInstance
  letI : IsNoetherianRing (TerminalMultiblockLaurentRing R Keep h) :=
    multivariateLaurent_isNoetherian
      (TerminalMultiblockRetainedRing R Keep) h
  rw [terminalMultiblockRetainedCoefficientHom, ← Ideal.map_map]
  calc
    ((C.map (groupAlgebraC
      (TerminalMultiblockRetainedRing R Keep)
      (TerminalMultiblockDegree h))).map MvPolynomial.C).height =
        (C.map (groupAlgebraC
          (TerminalMultiblockRetainedRing R Keep)
          (TerminalMultiblockDegree h))).height :=
      mvPolynomial_height_map_C _
    _ = C.height := multivariateLaurent_height_map_C _ h C

/-- The retained contraction produced by global terminal elimination has at
least the height of the original ideal. -/
theorem terminalGlobalStirlingInvariant_retainedContraction_height_le
    (R Keep : Type*) [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] [Finite Keep]
    (h : ℕ) (d : Fin h → ℕ)
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun b ↦ d b + 1) Keep I)
    (hJ : IsTerminalGlobalStirlingInvariant R (Fin h)
      (fun b ↦ d b + 1) Keep I) :
    I.height ≤
      (terminalMultiblockRetainedContraction R Keep h d
        (I.map (terminalMultiblockLocalizationHom R Keep h d))).height := by
  let C := terminalMultiblockRetainedContraction R Keep h d
    (I.map (terminalMultiblockLocalizationHom R Keep h d))
  calc
    I.height ≤
        (I.map (terminalMultiblockLocalizationHom R Keep h d)).height :=
      terminalMultiblockLocalizationHom_height_le R Keep h d I
    _ = (C.map
          (terminalMultiblockRetainedCoefficientHom R Keep h d)).height := by
      rw [terminalGlobalStirlingInvariant_multiblockElimination
        R Keep h d I hgraded hJ]
    _ = C.height :=
      terminalMultiblockRetainedCoefficientHom_height_map R Keep h d C

end AbelFormalization
