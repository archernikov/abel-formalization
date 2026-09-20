import AbelFormalization.TerminalLocalizationNumericBridge
import AbelFormalization.FiniteAnalyticChangeOfGenerators
import AbelFormalization.PolynomialGermSymbolMaps

/-!
# Finite analytic representatives for terminal localization

The denominator-cleared localization identity is an equality between finitely
many polynomials over analytic germs.  This file chooses actual analytic
representatives only for the terminal generators and the finitely many
localization coefficients.  A caller may supply representatives of the
contracted time generators, so the same representatives that produced the
bottom time lower bound can be reused here.

All identities then hold on one common neighborhood and hence along every
parameter sequence converging to the analytic base point.  No evaluation map
on the whole analytic-germ ring is introduced.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped BigOperators Topology

namespace AbelFormalization

universe u v w z

/-- An eventual pointwise equality of two finite families transports an
inverse-power lower bound. -/
theorem HasInversePowerLowerBound.congr_of_eventually
    {X ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter X} {scale : X → ℝ} {f g : ι → X → ℝ}
    (hf : HasInversePowerLowerBound l scale f)
    (hfg : ∀ᶠ x in l, ∀ i, f i x = g i x) :
    HasInversePowerLowerBound l scale g := by
  obtain ⟨c, hc, M, hlower⟩ := hf
  refine ⟨c, hc, M, ?_⟩
  filter_upwards [hlower, hfg] with x hx heq
  have hfamily : (fun i : ι ↦ |f i x|) = fun i : ι ↦ |g i x| := by
    funext i
    rw [heq i]
  simpa only [finiteFamilyMaxAbs, hfamily] using hx

/-- The product of the first-derivative variables has its literal constant
polynomial as an analytic representative. -/
theorem analyticPolynomialGermHom_terminalFirstDerivativeProduct
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (h : ℕ) (higher : Fin h → ℕ) :
    analyticPolynomialGermHom x
        (terminalFirstDerivativeProduct (AnalyticGermAt x) (Fin h) h higher) =
      ((fun _ : E ↦ terminalFirstDerivativeProduct ℝ (Fin h) h higher) :
        Germ (𝓝 x)
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
  rw [terminalFirstDerivativeProduct_eq_prod,
    terminalFirstDerivativeProduct_eq_prod, map_prod]
  have hfun :
      (fun _ : E => ∏ b : Fin h,
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
          TerminalMultiblockSourceRing ℝ h higher (Fin h))) =
        ∏ b : Fin h, fun _ : E =>
          (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
            TerminalMultiblockSourceRing ℝ h higher (Fin h)) := by
    funext y
    simp only [Finset.prod_apply]
  rw [hfun]
  change (∏ b : Fin h, analyticPolynomialGermHom x
      (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩))) =
    Germ.coeRingHom (𝓝 x)
      (∏ b : Fin h, fun _ : E =>
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
          TerminalMultiblockSourceRing ℝ h higher (Fin h)))
  rw [map_prod]
  simp only [analyticPolynomialGermHom_X]
  apply Finset.prod_congr rfl
  intro b hb
  rfl

/-- Simultaneous actual representatives for a fixed terminal-localization
identity.  The contracted representatives are inputs because applications
already selected them while constructing the bottom time lower bound. -/
structure TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator)
    (contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ)
    (contracted_germ_eq : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))) where
  terminalRepresentative : Terminal → E →
    TerminalMultiblockSourceRing ℝ h higher (Fin h)
  coefficientRepresentative : Contracted → Terminal → E →
    TerminalMultiblockSourceRing ℝ h higher (Fin h)
  neighborhood : Set E
  neighborhood_open : IsOpen neighborhood
  base_mem : x ∈ neighborhood
  terminal_support_subset : ∀ j y,
    (terminalRepresentative j y).support ⊆ (terminalGenerator j).support
  coefficient_support_subset : ∀ a j y,
    (coefficientRepresentative a j y).support ⊆
      (data.coefficient a j).support
  terminal_coefficient_analytic : ∀ j e,
    AnalyticOnNhd ℝ (fun y ↦ (terminalRepresentative j y).coeff e)
      neighborhood
  coefficient_coefficient_analytic : ∀ a j e,
    AnalyticOnNhd ℝ (fun y ↦ (coefficientRepresentative a j y).coeff e)
      neighborhood
  terminal_germ_eq : ∀ j,
    analyticPolynomialGermHom x (terminalGenerator j) =
      (terminalRepresentative j : Germ (𝓝 x)
        (TerminalMultiblockSourceRing ℝ h higher (Fin h)))
  coefficient_germ_eq : ∀ a j,
    analyticPolynomialGermHom x (data.coefficient a j) =
      (coefficientRepresentative a j : Germ (𝓝 x)
        (TerminalMultiblockSourceRing ℝ h higher (Fin h)))
  polynomial_identity : ∀ y ∈ neighborhood, ∀ a,
    terminalFirstDerivativeProduct ℝ (Fin h) h higher ^
          certificate.denominatorExponent *
        MvPolynomial.rename Sum.inr (contractedRepresentative a y) =
      ∑ j, coefficientRepresentative a j y * terminalRepresentative j y
  evaluation_identity : ∀ y ∈ neighborhood, ∀ a,
      ∀ assignment : TerminalMultiblockSourceIndex h higher (Fin h) → ℝ,
    MvPolynomial.eval assignment
        (terminalFirstDerivativeProduct ℝ (Fin h) h higher ^
          certificate.denominatorExponent *
          MvPolynomial.rename Sum.inr (contractedRepresentative a y)) =
      ∑ j, MvPolynomial.eval assignment (coefficientRepresentative a j y) *
        MvPolynomial.eval assignment (terminalRepresentative j y)

/-- Every fixed localization identity over analytic germs admits the finite
representative package above. -/
theorem TerminalGeneratorBackwardIdentity.nonempty_analyticRepresentativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator)
    (contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ)
    (hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))) :
    Nonempty (data.AnalyticRepresentativeData x contractedRepresentative
      hcontracted) := by
  classical
  let polynomial : Terminal ⊕ (Contracted × Terminal) →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h) :=
    fun k ↦ match k with
      | Sum.inl j => terminalGenerator j
      | Sum.inr aj => data.coefficient aj.1 aj.2
  obtain ⟨representative, U, hUopen, hxU, hsupport, hanalytic, hgerm⟩ :=
    exists_analyticPolynomialRepresentatives x polynomial
  let terminalRepresentative : Terminal → E →
      TerminalMultiblockSourceRing ℝ h higher (Fin h) :=
    fun j ↦ representative (Sum.inl j)
  let coefficientRepresentative : Contracted → Terminal → E →
      TerminalMultiblockSourceRing ℝ h higher (Fin h) :=
    fun a j ↦ representative (Sum.inr (a, j))
  have hterminalGerm : ∀ j,
      analyticPolynomialGermHom x (terminalGenerator j) =
        (terminalRepresentative j : Germ (𝓝 x)
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
    intro j
    simpa only [terminalRepresentative, polynomial] using hgerm (Sum.inl j)
  have hcoefficientGerm : ∀ a j,
      analyticPolynomialGermHom x (data.coefficient a j) =
        (coefficientRepresentative a j : Germ (𝓝 x)
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
    intro a j
    simpa only [coefficientRepresentative, polynomial] using
      hgerm (Sum.inr (a, j))
  let targetRepresentative : Contracted → E →
      TerminalMultiblockSourceRing ℝ h higher (Fin h) := fun a y ↦
    terminalFirstDerivativeProduct ℝ (Fin h) h higher ^
          certificate.denominatorExponent *
        MvPolynomial.rename Sum.inr (contractedRepresentative a y)
  have htargetGerm : ∀ a,
      analyticPolynomialGermHom x
          (terminalFirstDerivativeProduct (AnalyticGermAt x) (Fin h) h higher ^
              certificate.denominatorExponent *
            terminalMultiblockRetainedSourceHom (AnalyticGermAt x) (Fin h)
              h higher (contractedGenerator a)) =
        (targetRepresentative a : Germ (𝓝 x)
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
    intro a
    have hretained :
        analyticPolynomialGermHom x
            (terminalMultiblockRetainedSourceHom (AnalyticGermAt x) (Fin h)
              h higher (contractedGenerator a)) =
          ((fun y => MvPolynomial.rename
              (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
              (contractedRepresentative a y)) : Germ (𝓝 x)
            (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
      change analyticPolynomialGermHom x
          (MvPolynomial.rename
            (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
            (contractedGenerator a)) = _
      exact analyticPolynomialGermHom_rename_of x
        (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h))
        (hcontracted a)
    rw [map_mul, map_pow,
      analyticPolynomialGermHom_terminalFirstDerivativeProduct, hretained]
    exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun y => rfl)
  have heventual : ∀ a, targetRepresentative a =ᶠ[𝓝 x]
      fun y ↦ ∑ j,
        coefficientRepresentative a j y * terminalRepresentative j y := by
    intro a
    apply analyticPolynomialIdentity_eventually x Finset.univ
      (terminalFirstDerivativeProduct (AnalyticGermAt x) (Fin h) h higher ^
          certificate.denominatorExponent *
        terminalMultiblockRetainedSourceHom (AnalyticGermAt x) (Fin h)
          h higher (contractedGenerator a))
      (data.coefficient a) terminalGenerator
      (targetRepresentative a) (coefficientRepresentative a)
      terminalRepresentative
    · exact htargetGerm a
    · intro j _hj
      exact hcoefficientGerm a j
    · intro j _hj
      exact hterminalGerm j
    · simpa using data.identity a
  obtain ⟨V, hVopen, hxV, hpolynomial, hevaluation⟩ :=
    exists_open_polynomialIdentities_forall_eval x targetRepresentative
      (fun a y ↦ ∑ j,
        coefficientRepresentative a j y * terminalRepresentative j y)
      heventual
  refine ⟨{
    terminalRepresentative := terminalRepresentative
    coefficientRepresentative := coefficientRepresentative
    neighborhood := U ∩ V
    neighborhood_open := hUopen.inter hVopen
    base_mem := ⟨hxU, hxV⟩
    terminal_support_subset := ?_
    coefficient_support_subset := ?_
    terminal_coefficient_analytic := ?_
    coefficient_coefficient_analytic := ?_
    terminal_germ_eq := hterminalGerm
    coefficient_germ_eq := hcoefficientGerm
    polynomial_identity := ?_
    evaluation_identity := ?_
  }⟩
  · intro j y
    simpa only [terminalRepresentative, polynomial] using
      hsupport (Sum.inl j) y
  · intro a j y
    simpa only [coefficientRepresentative, polynomial] using
      hsupport (Sum.inr (a, j)) y
  · intro j e y hy
    exact hanalytic (Sum.inl j) e y hy.1
  · intro a j e y hy
    exact hanalytic (Sum.inr (a, j)) e y hy.1
  · intro y hy a
    exact hpolynomial y hy.2 a
  · intro y hy a assignment
    simpa only [targetRepresentative, map_sum, map_mul] using
      hevaluation y hy.2 a assignment

/-- Canonical choice of the finite terminal-localization representative
package. -/
noncomputable def TerminalGeneratorBackwardIdentity.analyticRepresentativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    (data : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator)
    (contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ)
    (hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))) :
    data.AnalyticRepresentativeData x contractedRepresentative hcontracted :=
  Classical.choice
    (data.nonempty_analyticRepresentativeData x contractedRepresentative
      hcontracted)

namespace TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData

universe q

/-- Numeric contracted-generator values, using the caller's retained-symbol
part of the terminal assignment. -/
def contractedValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (_data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type q} (parameter : X → E)
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (a : Contracted) (n : X) : ℝ :=
  MvPolynomial.eval (fun i ↦ symbolValue (Sum.inr i) n)
    (contractedRepresentative a (parameter n))

/-- Numeric terminal-generator values from the chosen representatives. -/
def terminalValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type q} (parameter : X → E)
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (j : Terminal) (n : X) : ℝ :=
  MvPolynomial.eval (fun z ↦ symbolValue z n)
    (data.terminalRepresentative j (parameter n))

/-- Numeric localization-coefficient values from the chosen representatives. -/
def coefficientValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type q} (parameter : X → E)
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (a : Contracted) (j : Terminal) (n : X) : ℝ :=
  MvPolynomial.eval (fun z ↦ symbolValue z n)
    (data.coefficientRepresentative a j (parameter n))

/-- Numeric value of the first derivative in one block. -/
def firstDerivativeValue
    {h : ℕ} {higher : Fin h → ℕ} {X : Type q}
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (d : Fin h) (n : X) : ℝ :=
  symbolValue (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩) n

/-- The algebraic localization identity becomes an eventual numeric identity
along every convergent analytic parameter family. -/
theorem eventually_numeric_identity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ) :
    ∀ᶠ n in l, ∀ a : Contracted,
      (∏ d, firstDerivativeValue symbolValue d n) ^
          certificate.denominatorExponent *
          data.contractedValue parameter symbolValue a n =
        ∑ j, data.coefficientValue parameter symbolValue a j n *
          data.terminalValue parameter symbolValue j n := by
  have hneighborhood : ∀ᶠ n in l, parameter n ∈ data.neighborhood :=
    hparameter.eventually (data.neighborhood_open.mem_nhds data.base_mem)
  filter_upwards [hneighborhood] with n hn
  intro a
  simpa [firstDerivativeValue, contractedValue, coefficientValue,
    terminalValue, terminalFirstDerivativeProduct_eq_prod,
    MvPolynomial.eval_rename, Function.comp_def] using
      data.evaluation_identity (parameter n) hn a
        (fun z ↦ symbolValue z n)

/-- Every chosen localization coefficient is polynomially bounded under a
polynomially bounded terminal symbol assignment. -/
theorem coefficientValue_hasPolynomialUpperBound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Fintype Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ z, HasPolynomialUpperBound l scale (symbolValue z))
    (a : Contracted) (j : Terminal) :
    HasPolynomialUpperBound l scale
      (data.coefficientValue parameter symbolValue a j) := by
  exact analyticMvPolynomialEvaluation_hasPolynomialUpperBound
    (data.coefficientRepresentative a j) (backward.coefficient a j).support
    data.neighborhood x data.base_mem parameter hparameter
    (data.coefficient_support_subset a j)
    (fun e _he ↦ data.coefficient_coefficient_analytic a j e)
    symbolValue hscale hsymbol

/-- Fully automatic terminal-localization transport from the supplied
contracted representatives.  The eventual identity and all localization
coefficient bounds are discharged by the finite analytic package. -/
theorem terminalValue_lower_of_contractedValue_lower
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {h : ℕ} {higher : Fin h → ℕ}
    {Q : Ideal (CentralPolynomial (AnalyticGermAt x) (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    {certificate : TerminalizedClusterCertificate (AnalyticGermAt x) h higher Q}
    {Contracted Terminal : Type}
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {contractedGenerator : Contracted →
      MvPolynomial (Fin h) (AnalyticGermAt x)}
    {terminalGenerator : Terminal →
      TerminalMultiblockSourceRing (AnalyticGermAt x) h higher (Fin h)}
    {backward : TerminalGeneratorBackwardIdentity (AnalyticGermAt x) higher
      certificate contractedGenerator terminalGenerator}
    {contractedRepresentative : Contracted → E → MvPolynomial (Fin h) ℝ}
    {hcontracted : ∀ a,
      analyticPolynomialGermHom x (contractedGenerator a) =
        (contractedRepresentative a :
          Germ (𝓝 x) (MvPolynomial (Fin h) ℝ))}
    (data : backward.AnalyticRepresentativeData x contractedRepresentative
      hcontracted)
    {X : Type} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : TerminalMultiblockSourceIndex h higher (Fin h) → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ z, HasPolynomialUpperBound l scale (symbolValue z))
    (hfirst : ∀ d,
      HasScalarInversePowerLowerBound l scale
        (firstDerivativeValue symbolValue d))
    (hcontractedLower : HasInversePowerLowerBound l scale
      (data.contractedValue parameter symbolValue)) :
    HasInversePowerLowerBound l scale
      (data.terminalValue parameter symbolValue) := by
  exact backward.terminal_lower_of_numeric_identity
    (data.contractedValue parameter symbolValue)
    (data.terminalValue parameter symbolValue)
    (firstDerivativeValue symbolValue)
    (data.coefficientValue parameter symbolValue)
    hscale hfirst
    (fun a j ↦ data.coefficientValue_hasPolynomialUpperBound parameter
      hparameter symbolValue hscale hsymbol a j)
    (data.eventually_numeric_identity parameter hparameter symbolValue)
    hcontractedLower

end TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData

end AbelFormalization
