import AbelFormalization.RestrictedRankEliminationTraceBoundary
import AbelFormalization.PaperRankClusterCurrying

/-!
# Finite trace data for the retained central iterations

`TerminalizedClusterCertificate` records its intermediate central operations
only through an iterate.  Quantitative transfer has to be applied once to
each of those operations.  This file exposes the ideal before every retained
central step, its unused-representative extension, and a nonempty finite
quantitative-transfer certificate for every actual step.

The construction is purely algebraic.  It does not add evaluation data or
analytic hypotheses.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

universe u v

namespace TerminalizedClusterCertificate

/-- The retained central ideal after exactly `j` additional simultaneous
central operations. -/
def centralIterationIdeal
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    (j : ℕ) :
    Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h)) :=
  (retainedCentralStep R (terminalTotalDerivativeCount higher)
    (Fin h))^[j] Q

@[simp]
theorem centralIterationIdeal_zero
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q) :
    certificate.centralIterationIdeal 0 = Q := by
  simp [centralIterationIdeal]

theorem centralIterationIdeal_succ
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    (j : ℕ) :
    certificate.centralIterationIdeal (j + 1) =
      retainedCentralStep R (terminalTotalDerivativeCount higher) (Fin h)
        (certificate.centralIterationIdeal j) := by
  simp only [centralIterationIdeal, Function.iterate_succ_apply']

/-- The input to quantitative transfer for retained central step `j`: the
current retained ideal with fresh, unused representative variables adjoined.
-/
def centralIterationTransferInput
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    (j : ℕ) :
    Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R) :=
  unusedRepresentativeExtension R (terminalTotalDerivativeCount higher)
    (Fin h) (certificate.centralIterationIdeal j)

/-- Central construction of the displayed transfer input is exactly the
next retained ideal. -/
theorem centralIdealConstruction_transferInput
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    (j : ℕ) :
    centralIdealConstruction
        (centralTransferShear (terminalTotalDerivativeCount higher))
        (certificate.centralIterationTransferInput j) =
      certificate.centralIterationIdeal (j + 1) := by
  rw [← negativeTerminalWeight_eq_centralTransferShear]
  change centralIdealConstruction
      (negativeTerminalWeight (terminalTotalDerivativeCount higher) (Fin h))
      (unusedRepresentativeExtension R
        (terminalTotalDerivativeCount higher) (Fin h)
        (certificate.centralIterationIdeal j)) = _
  calc
    _ = retainedCentralStep R (terminalTotalDerivativeCount higher) (Fin h)
          (certificate.centralIterationIdeal j) :=
      (retainedCentralStep_eq_centralIdealConstruction_unusedExtension
        R (terminalTotalDerivativeCount higher) (Fin h)
        (certificate.centralIterationIdeal j)).symm
    _ = certificate.centralIterationIdeal (j + 1) :=
      (certificate.centralIterationIdeal_succ j).symm

/-- The last ideal of the exposed iteration is the terminal ideal stored in
the certificate. -/
theorem centralIterationIdeal_extraSteps
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q) :
    certificate.centralIterationIdeal certificate.extraSteps =
      certificate.terminalIdeal := by
  exact certificate.terminal_eq_actualCentralIterate.symm

/-- A nonempty quantitative-transfer family for every retained central step
stored in a terminalized cluster certificate. -/
structure CentralIterationTransferData
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q) where
  transferCertificate : (j : Fin certificate.extraSteps) →
    CentralQuantitativeTransferCertificate R (Fin h) (Fin h)
      (terminalTotalDerivativeCount higher) h
      (centralTransferShear (terminalTotalDerivativeCount higher))
      (certificate.centralIterationTransferInput j)
  source_nonempty : ∀ j, Nonempty (Fin (transferCertificate j).count)

/-- Noetherianity chooses all finite transfer families after the algebraic
terminalization and before any sequence or analytic estimate is selected. -/
theorem nonempty_centralIterationTransferData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q) :
    Nonempty certificate.CentralIterationTransferData := by
  classical
  choose transferCertificate source_nonempty using
    fun j : Fin certificate.extraSteps ↦
      exists_nonempty_centralQuantitativeTransferCertificate
        (centralTransferShear (terminalTotalDerivativeCount higher))
        (certificate.centralIterationTransferInput j)
  exact ⟨{
    transferCertificate := transferCertificate
    source_nonempty := source_nonempty
  }⟩

/-- The central polynomials chosen at retained step `j` span the actual next
ideal in the stored iteration. -/
theorem CentralIterationTransferData.central_span_eq_next
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate R h higher Q}
    (data : certificate.CentralIterationTransferData)
    (j : Fin certificate.extraSteps) :
    Ideal.span (Set.range (fun a ↦
        centralPolynomialPhi R (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h)
          (centralNormalizedInitialPolynomial
            (centralTransferShear (terminalTotalDerivativeCount higher))
            ((data.transferCertificate j).source a)))) =
      certificate.centralIterationIdeal (j + 1) := by
  exact (data.transferCertificate j).central_span.trans
    (certificate.centralIdealConstruction_transferInput j)

end TerminalizedClusterCertificate

namespace ClusterAlgebraicReductionCertificate

/-- The complete list of central-transfer inputs for one algebraic cluster.
Index zero is the certificate's original curried ideal.  The remaining
indices are the unused-representative extensions for the retained central
iterations stored by its terminalization. -/
def centralTransferInput
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I)
    (j : Fin (certificate.terminalized.extraSteps + 1)) :
    Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R) :=
  Fin.cases I
    (fun k ↦ certificate.terminalized.centralIterationTransferInput k) j

/-- The central ideal produced by each input in `centralTransferInput`.
The first output is the first central ideal; later outputs traverse the
retained iteration. -/
def centralTransferOutput
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I)
    (j : Fin (certificate.terminalized.extraSteps + 1)) :
    Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h)) :=
  Fin.cases (clusterFirstCentralIdeal R higher I)
    (fun k ↦ certificate.terminalized.centralIterationIdeal (k + 1)) j

/-- Every displayed input/output pair is one literal central construction
with the quantitative-transfer shear. -/
theorem centralIdealConstruction_input_eq_output
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I)
    (j : Fin (certificate.terminalized.extraSteps + 1)) :
    centralIdealConstruction
        (centralTransferShear (terminalTotalDerivativeCount higher))
        (certificate.centralTransferInput j) =
      certificate.centralTransferOutput j := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · exact (clusterFirstCentralIdeal_eq_transfer higher I).symm
  · exact certificate.terminalized.centralIdealConstruction_transferInput k

/-- Nonempty finite quantitative-transfer certificates for the first central
operation and every retained central iteration of a cluster. -/
structure FullCentralTransferData
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I) where
  transferCertificate :
    (j : Fin (certificate.terminalized.extraSteps + 1)) →
      CentralQuantitativeTransferCertificate R (Fin h) (Fin h)
        (terminalTotalDerivativeCount higher) h
        (centralTransferShear (terminalTotalDerivativeCount higher))
        (certificate.centralTransferInput j)
  source_nonempty : ∀ j, Nonempty (Fin (transferCertificate j).count)

/-- Noetherianity chooses all transfer families for the full central trace at
once. -/
theorem nonempty_fullCentralTransferData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    (certificate : ClusterAlgebraicReductionCertificate R h higher I) :
    Nonempty certificate.FullCentralTransferData := by
  classical
  choose transferCertificate source_nonempty using
    fun j : Fin (certificate.terminalized.extraSteps + 1) ↦
      exists_nonempty_centralQuantitativeTransferCertificate
        (centralTransferShear (terminalTotalDerivativeCount higher))
        (certificate.centralTransferInput j)
  exact ⟨{
    transferCertificate := transferCertificate
    source_nonempty := source_nonempty
  }⟩

/-- At every central operation, the chosen central polynomials span the
actual output ideal in the cluster trace. -/
theorem FullCentralTransferData.central_span_eq_output
    {R : Type u} [CommRing R]
    {h : ℕ} {higher : Fin h → ℕ}
    {I : Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h)
        (terminalTotalDerivativeCount higher) (Fin h)) R)}
    {certificate : ClusterAlgebraicReductionCertificate R h higher I}
    (data : certificate.FullCentralTransferData)
    (j : Fin (certificate.terminalized.extraSteps + 1)) :
    Ideal.span (Set.range (fun a ↦
        centralPolynomialPhi R (Fin h)
          (terminalTotalDerivativeCount higher) (Fin h)
          (centralNormalizedInitialPolynomial
            (centralTransferShear (terminalTotalDerivativeCount higher))
            ((data.transferCertificate j).source a)))) =
      certificate.centralTransferOutput j := by
  exact (data.transferCertificate j).central_span.trans
    (certificate.centralIdealConstruction_input_eq_output j)

end ClusterAlgebraicReductionCertificate

end AbelFormalization
