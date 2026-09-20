import AbelFormalization.TerminalReindexedInvariantBridge
import AbelFormalization.TerminalInitialDehomogenizationCompatibility
import AbelFormalization.TerminalLocalizationCertificate
import AbelFormalization.TerminalGlobalHeightReduction
import AbelFormalization.IdealHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Algebraic reduction for one separated cluster

This module packages the algebraic part of one cluster reduction.  Starting
with a retained central ideal, it fully homogenizes, runs the finite
Noetherian terminal iteration, applies the exact number of homogeneous
central steps, sets the homogenizing variable equal to one, and performs
terminal localization and contraction.

The resulting certificate deliberately retains the terminal ideal, the time
ideal, the number of additional central steps, the localized equality, and a
common first-derivative denominator.  These are the data needed to transport
finite polynomial identities backwards in the later analytic argument.

Compatibility of terminal initial formation with `H = 1` is obtained from
ordinary homogeneity by the maintained homogeneous compatibility theorem.
-/

noncomputable section

namespace AbelFormalization

universe u v

open scoped Pointwise

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Layout and the retained inclusion into the terminal source -/

/-- If `higher b` is the number of derivatives above the first one in block
`b`, this is the total number of positive derivative variables in that
block. -/
abbrev terminalTotalDerivativeCount {h : Nat}
    (higher : Fin h -> Nat) : Fin h -> Nat :=
  fun b => higher b + 1

/-- Include the retained polynomial variables in the original terminal
source ring. -/
def terminalMultiblockRetainedSourceHom
    (R Keep : Type*) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat) :
    MvPolynomial Keep R →+*
      TerminalMultiblockSourceRing R h higher Keep :=
  (MvPolynomial.rename
    (Sum.inr : Keep -> TerminalMultiblockSourceIndex h higher Keep)).toRingHom

@[simp]
theorem terminalMultiblockRetainedSourceHom_C
    (R Keep : Type*) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat) (r : R) :
    terminalMultiblockRetainedSourceHom R Keep h higher
        (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [terminalMultiblockRetainedSourceHom]

@[simp]
theorem terminalMultiblockRetainedSourceHom_X
    (R Keep : Type*) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat) (k : Keep) :
    terminalMultiblockRetainedSourceHom R Keep h higher
        (MvPolynomial.X k) =
      MvPolynomial.X (Sum.inr k) := by
  simp [terminalMultiblockRetainedSourceHom]

/-- Localizing the retained-variable inclusion is exactly the retained
coefficient homomorphism used by terminal elimination. -/
theorem terminalMultiblockLocalizationHom_comp_retainedSourceHom
    (R Keep : Type*) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat) :
    (terminalMultiblockLocalizationHom R Keep h higher).comp
        (terminalMultiblockRetainedSourceHom R Keep h higher) =
      terminalMultiblockRetainedCoefficientHom R Keep h higher := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [terminalMultiblockRetainedSourceHom,
      terminalMultiblockRetainedCoefficientHom]
  · intro k
    simp [terminalMultiblockRetainedSourceHom,
      terminalMultiblockRetainedCoefficientHom]

/-- Ideal-level form of the same commuting triangle. -/
theorem terminalMultiblockRetainedSource_map_localization
    (R Keep : Type*) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat)
    (C : Ideal (MvPolynomial Keep R)) :
    (C.map (terminalMultiblockRetainedSourceHom R Keep h higher)).map
        (terminalMultiblockLocalizationHom R Keep h higher) =
      C.map (terminalMultiblockRetainedCoefficientHom R Keep h higher) := by
  rw [Ideal.map_map,
    terminalMultiblockLocalizationHom_comp_retainedSourceHom]

/-! ## Height monotonicity for the actual retained central step -/

/-- A retained central step cannot lower height.  This is the height theorem
for the full central construction, preceded by adjoining the unused
representative variables. -/
theorem retainedCentralStep_height_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v) [Finite Time]
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    K.height <= (retainedCentralStep R totalD Time K).height := by
  calc
    K.height =
        (unusedRepresentativeExtension R totalD Time K).height :=
      (unusedRepresentativeExtension_height R totalD Time K).symm
    _ <=
        (centralIdealConstruction
          (negativeTerminalWeight totalD Time)
          (unusedRepresentativeExtension R totalD Time K)).height :=
      centralIdealConstruction_height_le
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K)
    _ = (retainedCentralStep R totalD Time K).height :=
      congrArg Ideal.height
        (retainedCentralStep_eq_centralIdealConstruction_unusedExtension
          R totalD Time K).symm

/-- Every finite iterate of the retained central step has height at least the
height of its input. -/
theorem retainedCentralStep_iterate_height_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v) [Finite Time]
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    forall j : Nat,
      K.height <=
        ((retainedCentralStep R totalD Time)^[j] K).height := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans
        (retainedCentralStep_height_le totalD Time
          ((retainedCentralStep R totalD Time)^[j] K))

/-- The exact iterated dehomogenization identity only needs compatibility on
the ordinarily homogeneous ideals in the orbit.  This avoids the stronger
and generally unjustified assertion that terminal initial formation commutes
with `H = 1` for every ideal. -/
theorem homogeneousCentralStep_iterate_map_dehomogenization_of_isOrdinaryHomogeneous
    {R : Type u} [CommRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v)
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ => (1 : Nat))))
    (hcompat : forall L : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)),
      L.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule R
            (fun _ => (1 : Nat))) ->
        TerminalInitialDehomogenizationCompatible R totalD Time L) :
    forall j : Nat,
      homogeneousCentralDehomogenizeIdeal R totalD Time
          ((homogeneousCentralStep R totalD Time)^[j] K) =
        (retainedCentralStep R totalD Time)^[j]
          (homogeneousCentralDehomogenizeIdeal R totalD Time K) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      let F := homogeneousCentralStep R totalD Time
      let G := retainedCentralStep R totalD Time
      have hiterateHomogeneous :
          (F^[j] K).IsHomogeneous
            (MvPolynomial.weightedHomogeneousSubmodule R
              (fun _ => (1 : Nat))) := by
        exact homogeneousCentralStep_iterate_isOrdinaryHomogeneous
          R totalD Time K hK j
      calc
        homogeneousCentralDehomogenizeIdeal R totalD Time (F^[Nat.succ j] K) =
            homogeneousCentralDehomogenizeIdeal R totalD Time
              (F (F^[j] K)) :=
          congrArg (homogeneousCentralDehomogenizeIdeal R totalD Time)
            (Function.iterate_succ_apply' F j K)
        _ = G (homogeneousCentralDehomogenizeIdeal R totalD Time
              (F^[j] K)) :=
          homogeneousCentralStep_dehomogenizes_to_retainedCentralStep
            R totalD Time (F^[j] K)
              (hcompat (F^[j] K) hiterateHomogeneous)
        _ = G (G^[j]
              (homogeneousCentralDehomogenizeIdeal R totalD Time K)) :=
          congrArg G ih
        _ = G^[Nat.succ j]
              (homogeneousCentralDehomogenizeIdeal R totalD Time K) :=
          (Function.iterate_succ_apply' G j
            (homogeneousCentralDehomogenizeIdeal R totalD Time K)).symm

/-! ## Terminal invariants under the homogeneous time shear -/

/-- Mapping by the homogeneous time shear preserves closure under every
terminal multigraded component. -/
theorem homogeneousTimeShearIdeal_isTerminalMultigraded
    {R : Type u} [CommRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v)
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hI : IsTerminalMultigradedIdeal R (Fin h) totalD
      (Fin 1 ⊕ Time) I) :
    IsTerminalMultigradedIdeal R (Fin h) totalD (Fin 1 ⊕ Time)
      (homogeneousTimeShearIdeal R totalD Time I) := by
  intro P hP degree
  change P ∈
    I.map (homogeneousTimeShear R totalD Time).toRingHom at hP
  have hpre : (homogeneousTimeShear R totalD Time).symm P ∈ I :=
    (Ideal.symm_apply_mem_of_equiv_iff
      (I := I)
      (f := (homogeneousTimeShear R totalD Time).toRingEquiv)
      (y := P)).2 hP
  have hcomponent := hI _ hpre degree
  have hmap := Ideal.mem_map_of_mem
    (homogeneousTimeShear R totalD Time).toRingHom hcomponent
  change homogeneousTimeShear R totalD Time
      (terminalGlobalComponent R (Fin h) totalD (Fin 1 ⊕ Time)
        degree ((homogeneousTimeShear R totalD Time).symm P)) ∈ _ at hmap
  rw [homogeneousTimeShear_terminalGlobalComponent,
    (homogeneousTimeShear R totalD Time).apply_symm_apply] at hmap
  exact hmap

/-- The same statement for every finite iterate of the homogeneous time
shear. -/
theorem homogeneousTimeShearIdeal_iterate_isTerminalMultigraded
    {R : Type u} [CommRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v)
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hI : IsTerminalMultigradedIdeal R (Fin h) totalD
      (Fin 1 ⊕ Time) I) :
    forall j : Nat,
      IsTerminalMultigradedIdeal R (Fin h) totalD (Fin 1 ⊕ Time)
        ((homogeneousTimeShearIdeal R totalD Time)^[j] I) := by
  intro j
  induction j with
  | zero => simpa using hI
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact homogeneousTimeShearIdeal_isTerminalMultigraded
        totalD Time _ ih

/-- Exact fixedness under terminal Stirling is preserved by one homogeneous
time shear. -/
theorem homogeneousTimeShearIdeal_map_globalStirling_eq_of_fixed
    {R : Type u} [CommRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v)
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hfixed : I.map
      (terminalGlobalStirlingEquiv R (Fin h) totalD
        (Fin 1 ⊕ Time)).toRingHom = I) :
    (homogeneousTimeShearIdeal R totalD Time I).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom =
      homogeneousTimeShearIdeal R totalD Time I := by
  change
    (I.map (homogeneousTimeShear R totalD Time).toRingHom).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom =
      I.map (homogeneousTimeShear R totalD Time).toRingHom
  rw [ideal_map_homogeneousTimeShear_terminalGlobalStirling_commute,
    hfixed]

/-- Exact terminal-Stirling fixedness is preserved by every finite iterate
of the homogeneous time shear. -/
theorem homogeneousTimeShearIdeal_iterate_map_globalStirling_eq_of_fixed
    {R : Type u} [CommRing R]
    {h : Nat} (totalD : Fin h -> Nat) (Time : Type v)
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hfixed : I.map
      (terminalGlobalStirlingEquiv R (Fin h) totalD
        (Fin 1 ⊕ Time)).toRingHom = I) :
    forall j : Nat,
      ((homogeneousTimeShearIdeal R totalD Time)^[j] I).map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Time)).toRingHom =
        (homogeneousTimeShearIdeal R totalD Time)^[j] I := by
  intro j
  induction j with
  | zero => simpa using hfixed
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact homogeneousTimeShearIdeal_map_globalStirling_eq_of_fixed
        totalD Time _ ih

/-! ## The terminalized certificate -/

/-- Complete algebraic output of terminalizing one retained central ideal.
The denominator field records a common power which clears the extension of
the contracted time ideal back into the original terminal source ring. -/
structure TerminalizedClusterCertificate
    (R : Type u) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat)
    (Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))) where
  extraSteps : Nat
  terminalIdeal :
    Ideal (TerminalMultiblockSourceRing R h higher (Fin h))
  timeIdeal : Ideal (MvPolynomial (Fin h) R)
  coefficientIdeal : Ideal R
  terminal_eq_actualCentralIterate :
    terminalIdeal =
      (retainedCentralStep R (terminalTotalDerivativeCount higher)
        (Fin h))^[extraSteps] Q
  terminal_multigraded :
    IsTerminalMultigradedIdeal R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h) terminalIdeal
  terminal_stirling_fixed :
    terminalIdeal.map
        (terminalGlobalStirlingEquiv R (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h)).toRingHom =
      terminalIdeal
  terminal_stirling_invariant :
    IsTerminalGlobalStirlingInvariant R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h) terminalIdeal
  time_eq_retainedContraction :
    timeIdeal =
      terminalMultiblockRetainedContraction R (Fin h) h higher
        (terminalIdeal.map
          (terminalMultiblockLocalizationHom R (Fin h) h higher))
  localized_extension :
    terminalIdeal.map
        (terminalMultiblockLocalizationHom R (Fin h) h higher) =
      timeIdeal.map
        (terminalMultiblockRetainedCoefficientHom R (Fin h) h higher)
  coefficient_eq :
    coefficientIdeal = timeIdeal.comap MvPolynomial.C
  denominatorExponent : Nat
  denominator_clears_time_extension :
    terminalFirstDerivativeProduct R (Fin h) h higher ^
        denominatorExponent •
      timeIdeal.map
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher) <=
      terminalIdeal
  height_to_terminal : Q.height <= terminalIdeal.height
  height_to_time : Q.height <= timeIdeal.height
  height_loss : timeIdeal.height - h <= coefficientIdeal.height

/-- Construct the terminal certificate from precisely the finite
Noetherian-descent data.  Compatibility of terminal initial formation with
`H = 1` follows automatically along the ordinarily homogeneous orbit.

The chosen equivalence `e` is the finite enumeration needed by the maintained
descent theorem.  No cardinality choice is hidden in this statement. -/
theorem exists_terminalizedClusterCertificate
    {R : Type u} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    {h n krullDim : Nat} (higher : Fin h -> Nat)
    [Ring.KrullDimLE krullDim R]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n)
      (terminalTotalDerivativeCount higher) (Fin 1 ⊕ Fin h))
    (Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))) :
    Nonempty (TerminalizedClusterCertificate R h higher Q) := by
  let totalD : Fin h -> Nat := terminalTotalDerivativeCount higher
  have hcompat : forall K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Fin h)),
      K.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule R
            (fun _ => (1 : Nat))) ->
        TerminalInitialDehomogenizationCompatible R totalD (Fin h) K := by
    intro K hK
    exact
      terminalInitialDehomogenizationCompatible_of_isOrdinaryHomogeneous
        (R := R) (totalD := totalD) (Time := Fin h) K hK
  let QH := homogeneousCentralFullOrdinaryHomogenization
    R totalD (Fin h) Q
  have hQH : QH.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ => (1 : Nat))) := by
    dsimp only [QH]
    exact homogeneousCentralFullOrdinaryHomogenization_isHomogeneous
      R totalD (Fin h) Q
  obtain ⟨j0, hstableFixed, hstableMulti, _, _⟩ :=
    exists_homogeneousTerminalInitialIteration_stabilizes_with_invariants
      (R := R) totalD (Fin h) krullDim monomialOrder e QH hQH
  let stableIdeal :=
    homogeneousTerminalInitialIteration R totalD (Fin h) QH j0
  have hstableFixed' :
      stableIdeal.map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Fin h)).toRingHom = stableIdeal := by
    simpa only [stableIdeal] using hstableFixed
  have hstableMulti' :
      IsTerminalMultigradedIdeal R (Fin h) totalD
        (Fin 1 ⊕ Fin h) stableIdeal := by
    simpa only [stableIdeal] using hstableMulti
  let extraSteps := j0 + 1
  let actualHomogeneousIdeal :=
    (homogeneousCentralStep R totalD (Fin h))^[extraSteps] QH
  have hactual_eq_shear_stable :
      actualHomogeneousIdeal =
        (homogeneousTimeShearIdeal R totalD (Fin h))^[extraSteps]
          stableIdeal := by
    dsimp only [actualHomogeneousIdeal, extraSteps, stableIdeal]
    rw [homogeneousCentralStep_iterate_eq R totalD (Fin h) QH j0,
      hstableFixed]
  have hactualMulti :
      IsTerminalMultigradedIdeal R (Fin h) totalD
        (Fin 1 ⊕ Fin h) actualHomogeneousIdeal := by
    rw [hactual_eq_shear_stable]
    exact homogeneousTimeShearIdeal_iterate_isTerminalMultigraded
      totalD (Fin h) stableIdeal hstableMulti' extraSteps
  have hactualFixed :
      actualHomogeneousIdeal.map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Fin h)).toRingHom =
        actualHomogeneousIdeal := by
    rw [hactual_eq_shear_stable]
    exact
      homogeneousTimeShearIdeal_iterate_map_globalStirling_eq_of_fixed
        totalD (Fin h) stableIdeal hstableFixed' extraSteps
  let terminalIdeal := homogeneousCentralDehomogenizeIdeal
    R totalD (Fin h) actualHomogeneousIdeal
  have hterminalMulti :
      IsTerminalMultigradedIdeal R (Fin h) totalD (Fin h)
        terminalIdeal := by
    dsimp only [terminalIdeal]
    exact homogeneousCentralDehomogenization_isTerminalMultigradedIdeal
      (R := R) totalD (Fin h) actualHomogeneousIdeal hactualMulti
  have hterminalFixed :
      terminalIdeal.map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin h)).toRingHom = terminalIdeal := by
    dsimp only [terminalIdeal]
    exact
      homogeneousCentralDehomogenization_map_globalStirling_eq_of_fixed
        (R := R) totalD (Fin h) actualHomogeneousIdeal hactualFixed
  have hterminalInvariant :
      IsTerminalGlobalStirlingInvariant R (Fin h) totalD (Fin h)
        terminalIdeal := by
    dsimp only [terminalIdeal]
    exact
      homogeneousCentralDehomogenization_isTerminalGlobalStirlingInvariant
        (R := R) totalD (Fin h) actualHomogeneousIdeal hactualFixed
  have hQHdehom :
      homogeneousCentralDehomogenizeIdeal R totalD (Fin h) QH = Q := by
    simpa only [QH, homogeneousCentralDehomogenizeIdeal] using
      (homogeneousCentralFullOrdinaryHomogenization_map_dehomogenization
        R totalD (Fin h) Q)
  have hterminal_eq :
      terminalIdeal =
        (retainedCentralStep R totalD (Fin h))^[extraSteps] Q := by
    have hdehom :=
      homogeneousCentralStep_iterate_map_dehomogenization_of_isOrdinaryHomogeneous
        (R := R) totalD (Fin h) QH hQH hcompat extraSteps
    rw [hQHdehom] at hdehom
    simpa only [terminalIdeal, actualHomogeneousIdeal] using hdehom
  let timeIdeal :=
    terminalMultiblockRetainedContraction R (Fin h) h higher
      (terminalIdeal.map
        (terminalMultiblockLocalizationHom R (Fin h) h higher))
  let coefficientIdeal : Ideal R := timeIdeal.comap MvPolynomial.C
  have hlocalized :
      terminalIdeal.map
          (terminalMultiblockLocalizationHom R (Fin h) h higher) =
        timeIdeal.map
          (terminalMultiblockRetainedCoefficientHom R (Fin h) h higher) := by
    dsimp only [timeIdeal]
    exact terminalGlobalStirlingInvariant_multiblockElimination
      R (Fin h) h higher terminalIdeal hterminalMulti hterminalInvariant
  have hQterminal : Q.height <= terminalIdeal.height := by
    rw [hterminal_eq]
    exact retainedCentralStep_iterate_height_le
      totalD (Fin h) Q extraSteps
  have hterminalTime : terminalIdeal.height <= timeIdeal.height := by
    dsimp only [timeIdeal]
    exact
      terminalGlobalStirlingInvariant_retainedContraction_height_le
        R (Fin h) h higher terminalIdeal hterminalMulti hterminalInvariant
  have hQtime : Q.height <= timeIdeal.height :=
    hQterminal.trans hterminalTime
  have hheightLoss :
      timeIdeal.height - h <= coefficientIdeal.height := by
    have hcontract := mvPolynomial_height_sub_card_le_comap timeIdeal
    simpa only [Nat.card_fin, coefficientIdeal] using hcontract
  have htimeSourceLocalized :
      (timeIdeal.map
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher)).map
          (terminalMultiblockLocalizationHom R (Fin h) h higher) <=
        terminalIdeal.map
          (terminalMultiblockLocalizationHom R (Fin h) h higher) := by
    calc
      (timeIdeal.map
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher)).map
          (terminalMultiblockLocalizationHom R (Fin h) h higher) =
          timeIdeal.map
            (terminalMultiblockRetainedCoefficientHom
              R (Fin h) h higher) :=
        terminalMultiblockRetainedSource_map_localization
          R (Fin h) h higher timeIdeal
      _ <= terminalIdeal.map
          (terminalMultiblockLocalizationHom R (Fin h) h higher) :=
        hlocalized.symm.le
  have htimeSourceFG :
      (timeIdeal.map
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher)).FG := by
    exact Ideal.fg_of_isNoetherianRing _
  obtain ⟨denominatorExponent, hdenominator⟩ :=
    exists_common_firstDerivativeProduct_pow_smul_le
      R (Fin h) h higher
      (timeIdeal.map
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher))
      terminalIdeal htimeSourceFG htimeSourceLocalized
  refine ⟨{
    extraSteps := extraSteps
    terminalIdeal := terminalIdeal
    timeIdeal := timeIdeal
    coefficientIdeal := coefficientIdeal
    terminal_eq_actualCentralIterate := ?_
    terminal_multigraded := ?_
    terminal_stirling_fixed := ?_
    terminal_stirling_invariant := ?_
    time_eq_retainedContraction := rfl
    localized_extension := hlocalized
    coefficient_eq := rfl
    denominatorExponent := denominatorExponent
    denominator_clears_time_extension := hdenominator
    height_to_terminal := hQterminal
    height_to_time := hQtime
    height_loss := hheightLoss }⟩
  · simpa only [totalD] using hterminal_eq
  · simpa only [totalD] using hterminalMulti
  · simpa only [totalD] using hterminalFixed
  · simpa only [totalD] using hterminalInvariant

/-! ## Include the first central substitution -/

/-- The simultaneous central ideal formed from the cluster's representative
variables before the additional retained central iterations. -/
def clusterFirstCentralIdeal
    (R : Type u) [CommRing R]
    {h : Nat} (higher : Fin h -> Nat)
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)) :
    Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h)) :=
  centralIdealConstruction
    (negativeTerminalWeight
      (terminalTotalDerivativeCount higher) (Fin h)) I

/-- The full algebraic reduction certificate for one cluster, including its
first simultaneous central substitution. -/
structure ClusterAlgebraicReductionCertificate
    (R : Type u) [CommRing R]
    (h : Nat) (higher : Fin h -> Nat)
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)) where
  terminalized : TerminalizedClusterCertificate R h higher
    (clusterFirstCentralIdeal R higher I)
  height_monotone : I.height <= terminalized.timeIdeal.height
  height_after_contraction :
    I.height - h <= terminalized.coefficientIdeal.height

/-- Construct the full cluster reduction by applying the initial central
height theorem and then the retained terminalization certificate. -/
theorem exists_clusterAlgebraicReductionCertificate
    {R : Type u} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    {h n krullDim : Nat} (higher : Fin h -> Nat)
    [Ring.KrullDimLE krullDim R]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n)
      (terminalTotalDerivativeCount higher) (Fin 1 ⊕ Fin h))
    (I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)) :
    Nonempty (ClusterAlgebraicReductionCertificate R h higher I) := by
  let firstCentral := clusterFirstCentralIdeal R higher I
  obtain ⟨terminalized⟩ :=
    exists_terminalizedClusterCertificate
      (R := R) (h := h) (n := n) (krullDim := krullDim)
      higher monomialOrder e firstCentral
  have hfirst : I.height <= firstCentral.height := by
    dsimp only [firstCentral, clusterFirstCentralIdeal]
    exact centralIdealConstruction_height_le
      (negativeTerminalWeight
        (terminalTotalDerivativeCount higher) (Fin h)) I
  have htime : I.height <= terminalized.timeIdeal.height :=
    hfirst.trans terminalized.height_to_time
  refine ⟨{
    terminalized := terminalized
    height_monotone := htime
    height_after_contraction := ?_ }⟩
  exact (tsub_le_tsub_right htime (h : ENat)).trans
    terminalized.height_loss

/-- If the input has `q + h` units of height, contraction of the `h` time
variables leaves at least `q` units in the coefficient ring. -/
theorem clusterAlgebraicReduction_preserves_baseHeight
    {R : Type u} [CommRing R]
    {h q : Nat} {higher : Fin h -> Nat}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I)
    (hheight : (q : ENat) + (h : ENat) <= I.height) :
    (q : ENat) <= certificate.terminalized.coefficientIdeal.height := by
  exact
    (ENat.le_sub_of_add_le_right (ENat.natCast_ne_top h) hheight).trans
      certificate.height_after_contraction

end AbelFormalization
