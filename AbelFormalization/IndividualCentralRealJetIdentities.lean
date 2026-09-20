import AbelFormalization.IndividualCentralIdealTraceData
import AbelFormalization.OrderedClusterCentralRealJetIdentities

/-!
# Displayed identities for one individual logarithmic substitution

This is the finite-generator bridge for the selected-block construction.
It chooses a padded generating family on the translated curried source and
on the central core, records the two exact change-of-generators matrices, and
then transports both families back to the common flat block ring.  The source
transport uses the inverse coordinate translation; the central transport
re-adjoins the fresh representative variable.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization

universe u v

variable (R : Type u) [CommRing R]
variable {Block : Type v} [Fintype Block] [DecidableEq Block]

namespace IndividualCentralTransferData

/-- The translation `q ↦ q - 1` used before the selected-block initial
construction. -/
def sourceTranslation
    {d : Block → ℕ} (selected : Block) :
    MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing R d selected) ≃ₐ[
      IndividualCentralCoefficientRing R d selected]
    MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing R d selected) :=
  polynomialCoordinateTranslation
    (Sum.elim (fun _ : Fin 1 ↦
        (-1 : IndividualCentralCoefficientRing R d selected))
      (fun _ : CentralPolynomialIndex (Fin 1)
        (selectedBlockDerivativeCount d selected) (Fin 1) ↦ 0))

/-- Finite source and central presentations for one selected-block
quantitative transfer, with literal change-of-generators identities. -/
structure DisplayedData
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (transferData : IndividualCentralTransferData R d selected I) where
  source : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (IndividualCentralCoefficientRing R d selected))
    ((individualCentralCurriedIdeal R d selected I).map
      (sourceTranslation R selected).toRingHom)
  central : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
    (CentralPolynomial (IndividualCentralCoefficientRing R d selected)
      (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1))
    (individualCentralCoreIdeal R d selected I)
  identities : CentralTransferDisplayedIdentities transferData.certificate
    source.generator central.generator

/-- Noetherianity chooses both finite presentations and both exact
coefficient matrices. -/
theorem nonempty_displayedData
    [IsNoetherianRing R]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    (transferData : IndividualCentralTransferData R d selected I) :
    Nonempty (DisplayedData R transferData) := by
  classical
  let source := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ ((individualCentralCurriedIdeal R d selected I).map
        (sourceTranslation R selected).toRingHom))
  let central := Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily
      _ (individualCentralCoreIdeal R d selected I))
  let canonicalCentralGenerator : Fin transferData.certificate.count →
      CentralPolynomial (IndividualCentralCoefficientRing R d selected)
        (Fin 1) (selectedBlockDerivativeCount d selected) (Fin 1) :=
    centralGenerator R transferData
  have hsource : ∀ a, transferData.certificate.source a ∈
      Ideal.span (Set.range source.generator) := by
    intro a
    exact source.span_eq.ge (transferData.certificate.source_mem a)
  have hcanonicalSpan :
      Ideal.span (Set.range canonicalCentralGenerator) =
        individualCentralCoreIdeal R d selected I := by
    exact transferData.central_span_eq_core
  have hcentral : ∀ b, central.generator b ∈
      Ideal.span (Set.range canonicalCentralGenerator) := by
    intro b
    exact hcanonicalSpan.ge
      (central.span_eq.le Ideal.mem_span_range_self)
  let identities := Classical.choice
    (nonempty_centralTransferDisplayedIdentities
      transferData.certificate source.generator central.generator
      hsource hcentral)
  exact ⟨{ source := source, central := central, identities := identities }⟩

namespace DisplayedData

/-- Undo the preliminary translation and un-curry a displayed source
generator.  These are generators in the flat ideal before the decrement. -/
def beforeGenerator
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : DisplayedData R transferData)
    (k : Fin (data.source.count + 1)) :
    MvPolynomial (ClusterOperationSymbol Block d) R :=
  (selectedBlockCurryAlgEquiv R d selected).symm
    ((sourceTranslation R selected).symm (data.source.generator k))

/-- Re-adjoin the fresh representative and un-curry a displayed central
generator.  These are generators in the flat ideal after the decrement. -/
def afterGenerator
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : DisplayedData R transferData)
    (k : Fin (data.central.count + 1)) :
    MvPolynomial (ClusterOperationSymbol Block d) R :=
  (selectedBlockCurryAlgEquiv R d selected).symm
    (MvPolynomial.rename Sum.inr (data.central.generator k))

/-- The un-translated, un-curried source family spans the literal input
ideal. -/
theorem before_span
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : DisplayedData R transferData) :
    Ideal.span (Set.range (beforeGenerator R data)) = I := by
  let curry := selectedBlockCurryAlgEquiv R d selected
  let translate := sourceTranslation R (d := d) selected
  change Ideal.span (Set.range (fun k ↦
    curry.symm.toRingHom (translate.symm.toRingHom
      (data.source.generator k)))) = I
  calc
    Ideal.span (Set.range (fun k ↦
        curry.symm.toRingHom (translate.symm.toRingHom
          (data.source.generator k)))) =
        (Ideal.span (Set.range (fun k ↦
          translate.symm.toRingHom (data.source.generator k)))).map
            curry.symm.toRingHom := span_range_map_eq _ _
    _ = ((Ideal.span (Set.range data.source.generator)).map
          translate.symm.toRingHom).map curry.symm.toRingHom := by
      rw [span_range_map_eq]
    _ = (((individualCentralCurriedIdeal R d selected I).map
          translate.toRingHom).map translate.symm.toRingHom).map
            curry.symm.toRingHom := by rw [data.source.span_eq]
    _ = (individualCentralCurriedIdeal R d selected I).map
          curry.symm.toRingHom := by
      exact congrArg (fun J => J.map curry.symm.toRingHom)
        (Ideal.map_of_equiv translate.toRingEquiv)
    _ = I := by
      exact Ideal.map_of_equiv curry.toRingEquiv

/-- The re-extended, un-curried central family spans the literal output
ideal. -/
theorem after_span
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (data : DisplayedData R transferData) :
    Ideal.span (Set.range (afterGenerator R data)) =
      individualCentralIdealStep R d selected I := by
  let curry := selectedBlockCurryAlgEquiv R d selected
  let C := IndividualCentralCoefficientRing R d selected
  let d₁ := selectedBlockDerivativeCount d selected
  change Ideal.span (Set.range (fun k ↦
    curry.symm.toRingHom
      (MvPolynomial.rename Sum.inr (data.central.generator k)))) = _
  calc
    Ideal.span (Set.range (fun k ↦
        curry.symm.toRingHom
          (MvPolynomial.rename Sum.inr (data.central.generator k)))) =
      (Ideal.span (Set.range (fun k ↦
        MvPolynomial.rename Sum.inr (data.central.generator k)))).map
          curry.symm.toRingHom := span_range_map_eq _ _
    _ = (unusedRepresentativeExtension C d₁ (Fin 1)
          (Ideal.span (Set.range data.central.generator))).map
            curry.symm.toRingHom := by
      rw [span_rename_inr_range_eq_unusedPolynomialExtension]
      rfl
    _ = (unusedRepresentativeExtension C d₁ (Fin 1)
          (individualCentralCoreIdeal R d selected I)).map
            curry.symm.toRingHom := by rw [data.central.span_eq]
    _ = individualCentralIdealStep R d selected I := rfl

end DisplayedData
end IndividualCentralTransferData

/-! ## Displayed data along a whole fixed decrement list -/

/-- Simultaneous finite presentations and exact coefficient identities at
every boundary transition of an individual-decrement trace. -/
structure IndividualCentralDisplayedTraceData
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (traceData : IndividualCentralIdealTraceData R d steps I) where
  displayed : (j : Fin steps.length) →
    IndividualCentralTransferData.DisplayedData R (traceData.transferData j)

/-- Noetherianity chooses all displayed step data simultaneously. -/
theorem nonempty_individualCentralDisplayedTraceData
    [IsNoetherianRing R]
    (d : Block → ℕ) (steps : List Block)
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    (traceData : IndividualCentralIdealTraceData R d steps I) :
    Nonempty (IndividualCentralDisplayedTraceData R d steps I traceData) := by
  classical
  let displayed : (j : Fin steps.length) →
      IndividualCentralTransferData.DisplayedData R
        (traceData.transferData j) :=
    fun j ↦ Classical.choice
      (IndividualCentralTransferData.nonempty_displayedData R
        (traceData.transferData j))
  exact ⟨{ displayed := displayed }⟩

namespace IndividualCentralDisplayedTraceData

/-- The displayed family before step `j` spans its indexed before-ideal. -/
theorem before_span
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {traceData : IndividualCentralIdealTraceData R d steps I}
    (data : IndividualCentralDisplayedTraceData R d steps I traceData)
    (j : Fin steps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.DisplayedData.beforeGenerator R
        (data.displayed j))) =
      individualCentralIdealBefore R d steps I j := by
  exact IndividualCentralTransferData.DisplayedData.before_span R
    (data.displayed j)

/-- The displayed family after step `j` spans its indexed after-ideal. -/
theorem after_span
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {traceData : IndividualCentralIdealTraceData R d steps I}
    (data : IndividualCentralDisplayedTraceData R d steps I traceData)
    (j : Fin steps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.DisplayedData.afterGenerator R
        (data.displayed j))) =
      individualCentralIdealAfter R d steps I j := by
  exact IndividualCentralTransferData.DisplayedData.after_span R
    (data.displayed j)

/-- The same after-family spans the next boundary of the trace. -/
theorem after_span_boundary_succ
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {traceData : IndividualCentralIdealTraceData R d steps I}
    (data : IndividualCentralDisplayedTraceData R d steps I traceData)
    (j : Fin steps.length) :
    Ideal.span (Set.range
      (IndividualCentralTransferData.DisplayedData.afterGenerator R
        (data.displayed j))) =
      individualCentralIdealBoundary R d steps I j.succ := by
  exact (data.after_span R j).trans
    (individualCentralIdealAfter_eq_boundary R d steps I j)

end IndividualCentralDisplayedTraceData
end AbelFormalization
