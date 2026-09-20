import AbelFormalization.OrderedClusterAlgebraicDescent
import AbelFormalization.SeparatedFiniteRealJetTrace

/-!
# Natural-indexed data from an ordered cluster descent

The inductive ordered-cluster descent stores each algebraic certificate in a
nested `step`.  This module exposes the unique tail and certificate at every
natural stage below `orderedClusterCount`.  It also chooses padded finite
generating families for the terminal and time ideals and retains an arbitrary
caller-supplied generating family at the full-prefix endpoint.

All choices here are algebraic.  No evaluation or analytic identity is
introduced.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- A finite ideal presentation padded by a leading zero, so its index type
is nonempty even when the ideal is zero. -/
structure PaddedIdealGeneratorFamily
    (A : Type u) [CommRing A] (I : Ideal A) where
  count : ℕ
  generator : Fin (count + 1) → A
  span_eq : Ideal.span (Set.range generator) = I

/-- Every ideal of a Noetherian ring has a padded finite presentation. -/
theorem nonempty_paddedIdealGeneratorFamily
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    Nonempty (PaddedIdealGeneratorFamily A I) := by
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing I)
  exact ⟨{
    count := n
    generator := Fin.cons 0 g
    span_eq := (Ideal.span_range_finCons_zero g).trans hg
  }⟩

/-- Coefficient ring at natural prefix stage `j`. -/
abbrev OrderedClusterPrefixCoefficientRing
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher j : ℕ) :=
  data.OrderedClusterPrefixRing R higher j

/-- Drop the nested descent to any later prefix stage, retaining its ideal in
the dependent result. -/
def OrderedClusterPrefixAlgebraicDescent.tailAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj : k ≤ j) (hj : j ≤ data.orderedClusterCount) :
    Σ ideal : Ideal (data.OrderedClusterPrefixRing R higher j),
      OrderedClusterPrefixAlgebraicDescent R data higher initialIdeal
        j hj ideal := by
  induction descent generalizing j with
  | top =>
      have h : j = data.orderedClusterCount := Nat.le_antisymm hj hkj
      subst j
      exact ⟨initialIdeal, OrderedClusterPrefixAlgebraicDescent.top⟩
  | @step k hk nextIdeal tail certificate ih =>
      by_cases h : j = k
      · subst j
        exact ⟨certificate.terminalized.coefficientIdeal,
          OrderedClusterPrefixAlgebraicDescent.step k hk tail certificate⟩
      · exact ih j (by omega) hj

/-- The complete local view of one nonterminal step in a nested ordered
cluster descent. -/
structure OrderedClusterPrefixAlgebraicStage
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount))
    (j : ℕ) (hj : j < data.orderedClusterCount) where
  currentIdeal : Ideal (data.OrderedClusterPrefixRing R higher j)
  currentDescent : OrderedClusterPrefixAlgebraicDescent R data higher
    initialIdeal j (Nat.le_of_lt hj) currentIdeal
  nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (j + 1))
  tail : OrderedClusterPrefixAlgebraicDescent R data higher initialIdeal
    (j + 1) hj nextIdeal
  certificate : ClusterAlgebraicReductionCertificate
    (data.OrderedClusterPrefixRing R higher j)
    (data.orderedCluster ⟨j, hj⟩).card (fun _ ↦ higher)
    (data.orderedClusterPrefixCurriedIdeal R higher ⟨j, hj⟩ nextIdeal)
  currentIdeal_eq_coefficientIdeal :
    currentIdeal = certificate.terminalized.coefficientIdeal

/-- The coefficient ring left after the first `j` clusters have been
retained in the prefix. -/
abbrev OrderedClusterPrefixAlgebraicStage.CoefficientRing
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (_stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) :=
  data.OrderedClusterPrefixRing R higher j

/-- Number of blocks in the cluster eliminated at this stage. -/
def OrderedClusterPrefixAlgebraicStage.activeClusterSize
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (_stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) : ℕ :=
  (data.orderedCluster ⟨j, hj⟩).card

theorem OrderedClusterPrefixAlgebraicStage.activeClusterSize_pos
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) :
    0 < stage.activeClusterSize := by
  exact Finset.card_pos.mpr (data.orderedCluster_nonempty ⟨j, hj⟩)

/-- The predecessor needed by APIs which write a nonempty active cluster as
`Fin (m + 1)`. -/
def OrderedClusterPrefixAlgebraicStage.activeClusterTailSize
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) : ℕ :=
  stage.activeClusterSize - 1

theorem OrderedClusterPrefixAlgebraicStage.activeClusterTailSize_add_one
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) :
    stage.activeClusterTailSize + 1 = stage.activeClusterSize := by
  have := stage.activeClusterSize_pos
  unfold activeClusterTailSize
  omega

/-- The input ideal terminalized inside the stage certificate. -/
abbrev OrderedClusterPrefixAlgebraicStage.terminalizationInput
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) :=
  clusterFirstCentralIdeal stage.CoefficientRing (fun _ ↦ higher)
    (data.orderedClusterPrefixCurriedIdeal R higher ⟨j, hj⟩
      stage.nextIdeal)

/-- Extract the complete local view at every natural index below the ordered
cluster count. -/
def OrderedClusterPrefixAlgebraicDescent.stageAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (j : ℕ) (hj : j < data.orderedClusterCount) :
    OrderedClusterPrefixAlgebraicStage R data higher initialIdeal j hj := by
  obtain ⟨currentIdeal, currentDescent⟩ :=
    descent.tailAt j (Nat.zero_le _) (Nat.le_of_lt hj)
  cases currentDescent with
  | top => exact (Nat.lt_irrefl _ hj).elim
  | @step j hj nextIdeal tail certificate =>
      exact {
        currentIdeal := certificate.terminalized.coefficientIdeal
        currentDescent :=
          OrderedClusterPrefixAlgebraicDescent.step j hj tail certificate
        nextIdeal := nextIdeal
        tail := tail
        certificate := certificate
        currentIdeal_eq_coefficientIdeal := rfl
      }

/-- Padded finite presentations of both ideals displayed by one algebraic
cluster certificate. -/
structure OrderedClusterPrefixAlgebraicStage.DisplayedGenerators
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj) where
  terminal : PaddedIdealGeneratorFamily
    (TerminalMultiblockSourceRing
      (data.OrderedClusterPrefixRing R higher j)
      (data.orderedCluster ⟨j, hj⟩).card (fun _ ↦ higher)
      (Fin (data.orderedCluster ⟨j, hj⟩).card))
    stage.certificate.terminalized.terminalIdeal
  time : PaddedIdealGeneratorFamily
    (MvPolynomial (Fin (data.orderedCluster ⟨j, hj⟩).card)
      (data.OrderedClusterPrefixRing R higher j))
    stage.certificate.terminalized.timeIdeal

/-- Noetherianity supplies padded finite presentations for both ideals at a
chosen stage. -/
theorem OrderedClusterPrefixAlgebraicStage.nonempty_displayedGenerators
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj)
    [IsNoetherianRing (data.OrderedClusterPrefixRing R higher j)] :
    Nonempty stage.DisplayedGenerators := by
  exact ⟨{
    terminal := Classical.choice
      (nonempty_paddedIdealGeneratorFamily _
        stage.certificate.terminalized.terminalIdeal)
    time := Classical.choice
      (nonempty_paddedIdealGeneratorFamily _
        stage.certificate.terminalized.timeIdeal)
  }⟩

/-- The exact span fields choose a common-denominator localization identity
for the two displayed families, still before any evaluation is introduced. -/
theorem OrderedClusterPrefixAlgebraicStage.DisplayedGenerators.nonempty_backwardIdentity
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    {stage : OrderedClusterPrefixAlgebraicStage R data higher
      initialIdeal j hj}
    (generators : stage.DisplayedGenerators) :
    Nonempty (TerminalGeneratorBackwardIdentity stage.CoefficientRing
      (fun _ ↦ higher) stage.certificate.terminalized
      generators.time.generator generators.terminal.generator) := by
  exact
    stage.certificate.terminalized.nonempty_terminalGeneratorBackwardIdentity
      generators.time.generator generators.terminal.generator
      generators.time.span_eq generators.terminal.span_eq

/-- Natural-indexed finite presentations for every cluster stage, together
with a specified padded generating family at the full-prefix endpoint. -/
structure OrderedClusterPrefixAlgebraicDescent.DisplayedGenerators
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal) where
  stage : (j : ℕ) → (hj : j < data.orderedClusterCount) →
    (descent.stageAt j hj).DisplayedGenerators
  top : PaddedIdealGeneratorFamily
    (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)
    initialIdeal

/-- Choose all intermediate finite presentations while preserving a caller's
specified generating family at the full-prefix endpoint. -/
theorem OrderedClusterPrefixAlgebraicDescent.nonempty_displayedGenerators_of_top
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal)
    [∀ j, IsNoetherianRing (data.OrderedClusterPrefixRing R higher j)]
    (top : PaddedIdealGeneratorFamily
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)
      initialIdeal) :
    Nonempty descent.DisplayedGenerators := by
  let stages : (j : ℕ) → (hj : j < data.orderedClusterCount) →
      (descent.stageAt j hj).DisplayedGenerators :=
    fun j hj ↦ Classical.choice
      ((descent.stageAt j hj).nonempty_displayedGenerators)
  exact ⟨{ stage := stages, top := top }⟩

/-- Choose the full-prefix endpoint as well as every intermediate finite
presentation. -/
theorem OrderedClusterPrefixAlgebraicDescent.nonempty_displayedGenerators
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal)
    [∀ j, IsNoetherianRing (data.OrderedClusterPrefixRing R higher j)] :
    Nonempty descent.DisplayedGenerators := by
  exact descent.nonempty_displayedGenerators_of_top
    (Classical.choice
      (nonempty_paddedIdealGeneratorFamily _ initialIdeal))

end RepresentativeClusterSubsequence
end AbelFormalization
