import AbelFormalization.RankOneIdealAutomorphismWindow
import AbelFormalization.TerminalReindexedWindowStirling

set_option autoImplicit false

/-!
# Artinian descent for the reindexed terminal Stirling automorphism

This file supplies the ideal-level and exact-degree bridges needed to apply
`exists_lexicographicInitialIdealIteration_stabilizes_of_isArtinianRing` to
the terminal signed-Stirling automorphism.  The polynomial automorphism is
graded for ordinary total degree, its rank-one realization preserves each
exact degree piece and every bounded window, and its ordered-window action is
strictly lower triangular for the genuine terminal multidegree.
-/

noncomputable section

namespace AbelFormalization

universe u w

variable {B : Type u} [CommRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Ordinary homogeneity over the integral grading -/

/-- The integral constant-one weight of an exponent is its ordinary degree. -/
theorem finsupp_weight_one_int_eq_degree (m : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) m = (m.degree : ℤ) := by
  change Finsupp.weight (fun _ : Fin n ↦ ((1 : ℕ) : ℤ)) m =
    (m.degree : ℤ)
  rw [finsupp_weight_natCast (fun _ : Fin n ↦ (1 : ℕ)) m,
    ← Finsupp.degree_eq_weight_one]

/-- The terminal automorphism preserves the integral ordinary grading used
by homogeneous ideals. -/
theorem terminalReindexedGlobalStirlingEquiv_isWeightedHomogeneous_int
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) B} {degree : ℤ}
    (hP : P.IsWeightedHomogeneous (fun _ : Fin n ↦ (1 : ℤ)) degree) :
    (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e P).IsWeightedHomogeneous
        (fun _ : Fin n ↦ (1 : ℤ)) degree := by
  intro m hm
  obtain ⟨m₀, hm₀, hdegree⟩ :=
    terminalReindexedGlobalStirlingEquiv_coeff_degree
      (R := B) d Time e hm
  rw [finsupp_weight_one_int_eq_degree m, ← hdegree,
    ← finsupp_weight_one_int_eq_degree m₀]
  exact hP hm₀

/-- The inverse terminal automorphism preserves the same integral ordinary
grading. -/
theorem terminalReindexedGlobalStirlingEquiv_symm_isWeightedHomogeneous_int
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) B} {degree : ℤ}
    (hP : P.IsWeightedHomogeneous (fun _ : Fin n ↦ (1 : ℤ)) degree) :
    ((terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).symm P).IsWeightedHomogeneous
        (fun _ : Fin n ↦ (1 : ℤ)) degree := by
  intro m hm
  obtain ⟨m₀, hm₀, hdegree⟩ :=
    terminalReindexedGlobalStirlingEquiv_symm_coeff_degree
      (R := B) d Time e hm
  rw [finsupp_weight_one_int_eq_degree m, ← hdegree,
    ← finsupp_weight_one_int_eq_degree m₀]
  exact hP hm₀

/-- Mapping an ordinary-homogeneous ideal by the terminal automorphism keeps
it ordinary homogeneous. -/
theorem terminalReindexedGlobalStirlingEquiv_map_isHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ : Fin n ↦ (1 : ℤ)))) :
    (I.map (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingHom).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule B
          (fun _ : Fin n ↦ (1 : ℤ))) := by
  let grade := MvPolynomial.weightedHomogeneousSubmodule B
    (fun _ : Fin n ↦ (1 : ℤ))
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists grade I).mp hI
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  exact ⟨degree,
    terminalReindexedGlobalStirlingEquiv_isWeightedHomogeneous_int
      (B := B) d Time e hdegree⟩

/-! ## Restriction to an exact ordinary-degree piece -/

/-- The terminal rank-one module equivalence is the generic coordinatewise
module equivalence attached to the same polynomial algebra equivalence. -/
theorem terminalReindexedGlobalStirlingModuleEquiv_eq_polynomialAlgEquivModuleEquiv
    (e : TerminalFiniteReindex (n := n) d Time) :
    terminalReindexedGlobalStirlingModuleEquiv (R := B) d Time e =
      polynomialAlgEquivModuleEquiv (r := 1)
        (terminalReindexedGlobalStirlingEquiv (R := B) d Time e) :=
  rfl

/-- The terminal module equivalence preserves each exact ordinary-degree
ambient piece, not merely their bounded union. -/
theorem terminalReindexedGlobalStirlingModuleEquiv_map_ordinaryPiece
    (e : TerminalFiniteReindex (n := n) d Time) (degree : ℤ) :
    (artinianPolynomialModulePiece (B := B)
      (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree).map
        (terminalReindexedGlobalStirlingModuleEquiv
          (R := B) d Time e).toLinearMap =
      artinianPolynomialModulePiece (B := B)
        (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree := by
  let J := terminalReindexedGlobalStirlingModuleEquiv (R := B) d Time e
  let M := artinianPolynomialModulePiece (B := B)
    (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree
  have htermDegree (m : Fin n →₀ ℕ) :
      artinianPolynomialTermDegree (fun _ : Fin n ↦ 1)
          (fun _ : Fin 1 ↦ 0) ((0 : Fin 1), m) =
        (m.degree : ℤ) := by
    simp only [artinianPolynomialTermDegree, add_zero]
    rw [← Finsupp.degree_eq_weight_one]
  change M.map J.toLinearMap = M
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k m hm
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have hm' :
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e (P 0)).coeff m ≠ 0 := by
      change
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e (P 0)).coeff m ≠ 0 at hm
      exact hm
    obtain ⟨m₀, hm₀, hdegree⟩ :=
      terminalReindexedGlobalStirlingEquiv_coeff_degree
        (R := B) d Time e hm'
    have hterm₀ :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP 0 m₀ hm₀
    change artinianPolynomialTermDegree (fun _ : Fin n ↦ 1)
      (fun _ : Fin 1 ↦ 0) ((0 : Fin 1), m₀) = degree at hterm₀
    change artinianPolynomialTermDegree (fun _ : Fin n ↦ 1)
      (fun _ : Fin 1 ↦ 0) ((0 : Fin 1), m) = degree
    rw [htermDegree m, ← hdegree, ← htermDegree m₀]
    exact hterm₀
  · intro P hP
    refine ⟨J.symm P, ?_, J.apply_symm_apply P⟩
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k m hm
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have hm' :
        ((terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).symm (P 0)).coeff m ≠ 0 := by
      simpa only [J,
        terminalReindexedGlobalStirlingModuleEquiv_symm_apply] using hm
    obtain ⟨m₀, hm₀, hdegree⟩ :=
      terminalReindexedGlobalStirlingEquiv_symm_coeff_degree
        (R := B) d Time e hm'
    have hterm₀ :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP 0 m₀ hm₀
    change artinianPolynomialTermDegree (fun _ : Fin n ↦ 1)
      (fun _ : Fin 1 ↦ 0) ((0 : Fin 1), m₀) = degree at hterm₀
    change artinianPolynomialTermDegree (fun _ : Fin n ↦ 1)
      (fun _ : Fin 1 ↦ 0) ((0 : Fin 1), m) = degree
    rw [htermDegree m, ← hdegree, ← htermDegree m₀]
    exact hterm₀

/-- Restriction of a module equivalence to an invariant exact polynomial
degree piece. -/
def artinianPolynomialModulePieceRestriction
    {r : ℕ} (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (artinianPolynomialModulePiece (B := B) weight shift degree).map
        J.toLinearMap =
      artinianPolynomialModulePiece (B := B) weight shift degree) :
    artinianPolynomialModulePiece (B := B) weight shift degree ≃ₗ[B]
      artinianPolynomialModulePiece (B := B) weight shift degree :=
  J.ofSubmodules _ _ hJ

theorem artinianPolynomialModulePieceRestriction_symm_coe
    {r : ℕ} (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (artinianPolynomialModulePiece (B := B) weight shift degree).map
        J.toLinearMap =
      artinianPolynomialModulePiece (B := B) weight shift degree)
    (P : artinianPolynomialModulePiece (B := B) weight shift degree) :
    (artinianPolynomialModulePieceRestriction weight shift degree J hJ).symm P =
      ⟨J.symm P, by
        have himage :
            (P : artinianFreePolynomialModule B n r) ∈
              (artinianPolynomialModulePiece
                (B := B) weight shift degree).map J.toLinearMap := by
          rw [hJ]
          exact P.property
        rw [Submodule.mem_map_equiv] at himage
        exact himage⟩ := by
  apply (artinianPolynomialModulePieceRestriction
    weight shift degree J hJ).injective
  apply Subtype.ext
  simp [artinianPolynomialModulePieceRestriction]

/-- If an ambient equivalence preserves an exact degree piece and maps one
polynomial submodule to another, then it maps their exact-degree restrictions
onto one another. -/
theorem artinianPolynomialSubmoduleDegree_map_equiv
    {r : ℕ} (weight : Fin n → ℕ) (shift : Fin r → ℤ) (degree : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (artinianPolynomialModulePiece (B := B) weight shift degree).map
        J.toLinearMap =
      artinianPolynomialModulePiece (B := B) weight shift degree)
    (N N' : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hmap : N'.restrictScalars B =
      (N.restrictScalars B).map J.toLinearMap) :
    artinianPolynomialSubmoduleDegree N' weight shift degree =
      (artinianPolynomialSubmoduleDegree N weight shift degree).map
        (artinianPolynomialModulePieceRestriction
          weight shift degree J hJ).toLinearMap := by
  ext P
  rw [Submodule.mem_map_equiv]
  change (P : artinianFreePolynomialModule B n r) ∈ N' ↔
    (((artinianPolynomialModulePieceRestriction
        weight shift degree J hJ).symm P :
      artinianPolynomialModulePiece (B := B) weight shift degree) :
        artinianFreePolynomialModule B n r) ∈ N
  change (P : artinianFreePolynomialModule B n r) ∈ N'.restrictScalars B ↔
    (((artinianPolynomialModulePieceRestriction
        weight shift degree J hJ).symm P :
      artinianPolynomialModulePiece (B := B) weight shift degree) :
        artinianFreePolynomialModule B n r) ∈ N.restrictScalars B
  rw [hmap, Submodule.mem_map_equiv]
  change J.symm (P : artinianFreePolynomialModule B n r) ∈
      N.restrictScalars B ↔ _
  rw [artinianPolynomialModulePieceRestriction_symm_coe]

/-- Exact ordinary-degree slices of an ideal and its terminal image are
carried to one another by the restricted module equivalence. -/
theorem terminalReindexed_artinianPolynomialSubmoduleDegree_map
    (e : TerminalFiniteReindex (n := n) d Time) (degree : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    artinianPolynomialSubmoduleDegree
        (rankOnePolynomialIdealSubmodule
          (I.map (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingHom))
        (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree =
      (artinianPolynomialSubmoduleDegree
        (rankOnePolynomialIdealSubmodule I)
        (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree).map
          (artinianPolynomialModulePieceRestriction
            (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree
            (terminalReindexedGlobalStirlingModuleEquiv
              (R := B) d Time e)
            (terminalReindexedGlobalStirlingModuleEquiv_map_ordinaryPiece
              (B := B) d Time e degree)).toLinearMap := by
  apply artinianPolynomialSubmoduleDegree_map_equiv
    (B := B) (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree
    (terminalReindexedGlobalStirlingModuleEquiv (R := B) d Time e)
    (terminalReindexedGlobalStirlingModuleEquiv_map_ordinaryPiece
      (B := B) d Time e degree)
    (rankOnePolynomialIdealSubmodule I)
    (rankOnePolynomialIdealSubmodule
      (I.map (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingHom))
  simpa only [
    terminalReindexedGlobalStirlingModuleEquiv_eq_polynomialAlgEquivModuleEquiv]
    using rankOnePolynomialIdealSubmodule_map_algEquiv
      (terminalReindexedGlobalStirlingEquiv (R := B) d Time e) I

/-- The terminal automorphism preserves the module length of every exact
ordinary-degree slice. -/
theorem terminalReindexed_artinianPolynomialSubmoduleDegree_length
    (e : TerminalFiniteReindex (n := n) d Time) (degree : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (I.map (terminalReindexedGlobalStirlingEquiv
              (R := B) d Time e).toRingHom))
          (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree) =
      Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree) := by
  rw [terminalReindexed_artinianPolynomialSubmoduleDegree_map
    (B := B) d Time e degree I]
  exact length_map_linearEquiv _ _

/-! ## The ideal action on the ordered bounded window -/

/-- On every bounded ordered-weight part, mapping an ideal by the terminal
automorphism is the conjugated rank-one module action. -/
theorem terminalReindexed_polynomialWindowOrderedWeightPart_map
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    G.polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule
          (I.map (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingHom)) =
      (G.polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule I)).map
          (G.windowOrderedWeightConjugate hpositive D
            (terminalReindexedGlobalStirlingModuleEquiv
              (R := B) d Time e)
            (terminalReindexedGlobalStirlingModuleEquiv_map_window
              (R := B) d Time e D)).toLinearMap := by
  let G := terminalReindexedGradedLexData d Time e
  let hpositive : ∀ i : Fin n, 0 < G.ordinaryDegree i :=
    terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
  let J := terminalReindexedGlobalStirlingEquiv (R := B) d Time e
  let Jmodule := terminalReindexedGlobalStirlingModuleEquiv
    (R := B) d Time e
  change G.polynomialWindowOrderedWeightPart hpositive D
      (rankOnePolynomialIdealSubmodule (I.map J.toRingHom)) =
    (G.polynomialWindowOrderedWeightPart hpositive D
      (rankOnePolynomialIdealSubmodule I)).map
        (G.windowOrderedWeightConjugate hpositive D Jmodule
          (terminalReindexedGlobalStirlingModuleEquiv_map_window
            (R := B) d Time e D)).toLinearMap
  apply G.polynomialWindowOrderedWeightPart_map_equiv hpositive D Jmodule
    (terminalReindexedGlobalStirlingModuleEquiv_map_window
      (R := B) d Time e D)
    (rankOnePolynomialIdealSubmodule I)
    (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
  simpa only [Jmodule, J,
    terminalReindexedGlobalStirlingModuleEquiv_eq_polynomialAlgEquivModuleEquiv]
    using rankOnePolynomialIdealSubmodule_map_algEquiv J I

/-! ## Concrete Artinian stabilization -/

/-- The lexicographic-initial iteration for the reindexed terminal
signed-Stirling automorphism stabilizes over an Artinian coefficient ring
with a nilpotent maximal coefficient ideal. -/
theorem exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes
    [IsArtinianRing B]
    (monomialOrder : MonomialOrder (Fin n))
    (coefficientIdeal : Ideal B) [coefficientIdeal.IsMaximal]
    {exponent : ℕ} (hcoeff : coefficientIdeal ^ exponent = ⊥)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ : Fin n ↦ (1 : ℤ)))) :
    let multiDegree : Fin n → Fin h → ℤ := fun i b ↦
      ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)
    let J := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  let multiDegree : Fin n → Fin h → ℤ := fun i b ↦
    ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)
  let Jalg := terminalReindexedGlobalStirlingEquiv (R := B) d Time e
  let J := Jalg.toRingEquiv
  let Jmodule := terminalReindexedGlobalStirlingModuleEquiv
    (R := B) d Time e
  have hpositive : ∀ i : Fin n, 0 < (fun _ : Fin n ↦ 1) i := by
    intro i
    simp
  have hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun _ : Fin n ↦ (1 : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun _ : Fin n ↦ (1 : ℤ))) := by
    intro I hI
    have hmap := terminalReindexedGlobalStirlingEquiv_map_isHomogeneous
      (B := B) d Time e I hI
    simpa only [J, Jalg] using hmap
  have hJlength : ∀ (I : Ideal (MvPolynomial (Fin n) B)),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun _ : Fin n ↦ (1 : ℤ))) →
      ∀ degree : ℤ,
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
            (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree)).toNat =
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              (rankOnePolynomialIdealSubmodule I)
              (fun _ : Fin n ↦ 1) (fun _ : Fin 1 ↦ 0) degree)).toNat := by
    intro I _ degree
    have hlength :=
      terminalReindexed_artinianPolynomialSubmoduleDegree_length
        (B := B) d Time e degree I
    simpa only [J, Jalg] using
      congrArg ENat.toNat hlength
  have hJwindow : ∀ D : ℤ,
      ((rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).windowModule
          B hpositive D).map Jmodule.toLinearMap =
        (rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).windowModule
          B hpositive D := by
    intro D
    exact terminalReindexedGlobalStirlingModuleEquiv_map_window
      (R := B) d Time e D
  have hJtriangular : ∀ D : ℤ,
      (rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).IsWindowWeightTriangular
        hpositive D Jmodule := by
    intro D
    exact terminalReindexedGlobalStirlingModuleEquiv_isWindowWeightTriangular
      (R := B) d Time e D
  have hJpart : ∀ (D : ℤ) (I : Ideal (MvPolynomial (Fin n) B)),
      (rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).polynomialWindowOrderedWeightPart
          hpositive D (rankOnePolynomialIdealSubmodule (I.map J.toRingHom)) =
        ((rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).polynomialWindowOrderedWeightPart
          hpositive D (rankOnePolynomialIdealSubmodule I)).map
            ((rankOnePolynomialGradedLexData (fun _ : Fin n ↦ 1) multiDegree).windowOrderedWeightConjugate
              hpositive D Jmodule (hJwindow D)).toLinearMap := by
    intro D I
    exact terminalReindexed_polynomialWindowOrderedWeightPart_map
      (B := B) d Time e D I
  exact exists_lexicographicInitialIdealIteration_stabilizes_of_isArtinianRing
    monomialOrder coefficientIdeal hcoeff (fun _ : Fin n ↦ 1)
      multiDegree hpositive J Jmodule Q hQ
      hJordinary hJlength hJwindow hJtriangular hJpart

end AbelFormalization
