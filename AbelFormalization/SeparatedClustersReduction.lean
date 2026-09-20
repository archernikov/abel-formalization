import AbelFormalization.ClusterAlgebraicReduction
import AbelFormalization.FilteredFiniteHierarchy
import AbelFormalization.FiniteSupportCoefficientPerturbation
import AbelFormalization.LocalizationLowerBoundTransport
import AbelFormalization.PolynomialEventualLowerBound
import AbelFormalization.TerminalLocalizationIdentities
import Mathlib.Data.Nat.Nth

/-!
# Finite assembly for the separated-clusters reduction

This file isolates the part of Proposition `prop:separated` which follows
formally once the one-cluster algebraic reduction and the analytic estimates
for every chosen cluster have been supplied.

The results below prove four pieces of infrastructure:

* a common localization multiplier can be inserted before applying the
  existing finite linear-combination lower-bound theorem;
* finitely many backwards cluster steps compose without changing the order
  of the existential quantifiers in the proposition;
* the one-cluster height loss adds over the ordered list of clusters;
* a lower bound on `separatedRestriction Λ Γ N` is exactly the threshold
  statement on `Λ ∩ Γ N` used in the paper; and
* an `atTop` quantitative-transfer theorem applied to the increasing
  enumeration of an infinite restricted set descends to its restricted
  filter (with the finite case discharged by vacuity).

The file deliberately does not assert the full separated-clusters
proposition.  A concrete application must still construct the balancing
subsequence `Λ`, build the relabelled one-cluster ideals, evaluate the
terminal localization identities, and discharge the hierarchy and analytic
coefficient hypotheses of
`CentralQuantitativeTransferCertificate.realJet_quantitativeTransfer_of_analyticRepresentatives`
at every step.  Those are mathematical inputs, rather than consequences of
the finite assembly proved here.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v

variable {X : Type u}

/-! ## Clearing a common evaluated localization multiplier -/

/-- The analytic data needed to propagate a lower bound backwards through
one evaluated, denominator-cleared terminal-localization identity.

The algebraic identity itself is produced before evaluation by
`exists_common_firstDerivativeProduct_pow_generator_identities`.  In a
concrete application, `firstDerivative_lower` comes from lower bounds for
the first derivatives, while `coefficient_bound` comes from analytic
representatives of the finitely many coefficients. -/
structure DenominatorClearedBackwardStep
    {Derivative Contracted Terminal : Type v}
    [Fintype Derivative]
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    (l : Filter X) (R : X → ℝ)
    (contracted : Contracted → X → ℝ)
    (terminal : Terminal → X → ℝ) where
  firstDerivative : Derivative → X → ℝ
  exponent : ℕ
  coefficient : Contracted → Terminal → X → ℝ
  scale_ge_one : ∀ᶠ x in l, 1 ≤ R x
  firstDerivative_lower : ∀ d,
    HasScalarInversePowerLowerBound l R (firstDerivative d)
  coefficient_bound : HasUniformPolynomialUpperBound l R coefficient
  identity : ∀ᶠ x in l, ∀ a : Contracted,
    (∏ d, firstDerivative d x) ^ exponent * contracted a x =
      ∑ j, coefficient a j x * terminal j x

/-- Quantitative propagation through one evaluated localization-clearing
step. -/
theorem DenominatorClearedBackwardStep.propagate
    {Derivative Contracted Terminal : Type v}
    [Fintype Derivative]
    [Fintype Contracted] [Nonempty Contracted]
    [Fintype Terminal] [Nonempty Terminal]
    {l : Filter X} {R : X → ℝ}
    {contracted : Contracted → X → ℝ}
    {terminal : Terminal → X → ℝ}
    (step : DenominatorClearedBackwardStep (Derivative := Derivative)
      l R contracted terminal)
    (hlower : HasInversePowerLowerBound l R contracted) :
    HasInversePowerLowerBound l R terminal := by
  exact hasInversePowerLowerBound_of_clearedLocalizationIdentities
    step.firstDerivative step.exponent contracted terminal step.coefficient
    step.scale_ge_one step.firstDerivative_lower hlower
    step.coefficient_bound step.identity

/-! ## Finite backwards iteration -/

/-- A finite trace of already-verified one-cluster quantitative steps.

Stage `clusterCount` is the terminal seed and stage `0` is the generating
family appearing in the conclusion.  The implication in `step` is exactly
where a concrete proof invokes the one-cluster quantitative transfer,
localization clearing, and fixed changes of generators. -/
structure SeparatedClustersBackwardTrace
    (l : Filter X) (clusterCount : ℕ)
    (generatorCount : ℕ → ℕ)
    (scale : ℕ → X → ℝ)
    (value : (j : ℕ) → Fin (generatorCount j + 1) → X → ℝ) where
  step : ∀ j, j < clusterCount →
    HasInversePowerLowerBound l (scale (j + 1)) (value (j + 1)) →
      HasInversePowerLowerBound l (scale j) (value j)

/-- Finite decreasing induction composes all verified backwards cluster
steps. -/
theorem SeparatedClustersBackwardTrace.initial_of_terminal
    {l : Filter X} {clusterCount : ℕ}
    {generatorCount : ℕ → ℕ}
    {scale : ℕ → X → ℝ}
    {value : (j : ℕ) → Fin (generatorCount j + 1) → X → ℝ}
    (trace : SeparatedClustersBackwardTrace l clusterCount
      generatorCount scale value)
    (hterminal : HasInversePowerLowerBound l (scale clusterCount)
      (value clusterCount)) :
    HasInversePowerLowerBound l (scale 0) (value 0) := by
  exact Nat.decreasingInduction
    (motive := fun j _ => HasInversePowerLowerBound l (scale j) (value j))
    (fun j hj hnext => trace.step j hj hnext)
    hterminal (Nat.zero_le clusterCount)

/-- If every backwards stage is just a denominator-cleared identity at one
common scale, the preceding abstract trace is obtained automatically. -/
def separatedClustersBackwardTrace_of_denominatorClearedSteps
    {l : Filter X} {clusterCount : ℕ}
    {generatorCount derivativeCount : ℕ → ℕ} {R : X → ℝ}
    {value : (j : ℕ) → Fin (generatorCount j + 1) → X → ℝ}
    (step : ∀ j, j < clusterCount →
      DenominatorClearedBackwardStep (Derivative := Fin (derivativeCount j))
        l R (value (j + 1)) (value j)) :
    SeparatedClustersBackwardTrace l clusterCount generatorCount
      (fun _ => R) value where
  step j hj := (step j hj).propagate

/-! ## Additivity of the algebraic height loss -/

/-- Total size of the clusters with indices strictly below `j`, expressed
directly in `ENat` to avoid a separate cast-of-sum argument. -/
def separatedClusterPrefixSize
    (clusterSize : ℕ → ℕ) (j : ℕ) : ENat :=
  (Finset.range j).sum (fun i => (clusterSize i : ENat))

/-- Numerical trace obtained by applying the one-cluster height estimate at
successive stages.  With the descending convention used here, stage
`clusterCount` is the original ideal and stage `0` is the final coefficient
ideal.  Each field `step j` is supplied by
`ClusterAlgebraicReductionCertificate.height_after_contraction`. -/
structure SeparatedClustersHeightTrace
    (clusterCount : ℕ) (clusterSize : ℕ → ℕ)
    (stageHeight : ℕ → ENat) where
  step : ∀ j, j < clusterCount →
    stageHeight (j + 1) - (clusterSize j : ENat) ≤ stageHeight j

/-- The one-cluster height losses add: height at least `p` plus the sum of
all cluster sizes at the original stage leaves height at least `p` in the
final coefficient stage. -/
theorem SeparatedClustersHeightTrace.baseHeight_le
    {clusterCount p : ℕ} {clusterSize : ℕ → ℕ}
    {stageHeight : ℕ → ENat}
    (trace : SeparatedClustersHeightTrace clusterCount clusterSize stageHeight)
    (hheight : (p : ENat) +
      separatedClusterPrefixSize clusterSize clusterCount ≤
        stageHeight clusterCount) :
    (p : ENat) ≤ stageHeight 0 := by
  have hzero : (p : ENat) + separatedClusterPrefixSize clusterSize 0 ≤
      stageHeight 0 := by
    exact Nat.decreasingInduction
      (motive := fun j _ => (p : ENat) +
        separatedClusterPrefixSize clusterSize j ≤ stageHeight j)
      (fun j hj hnext => by
        have hadd : ((p : ENat) + separatedClusterPrefixSize clusterSize j) +
            (clusterSize j : ENat) ≤ stageHeight (j + 1) := by
          simpa only [separatedClusterPrefixSize, Finset.sum_range_succ,
            add_assoc] using hnext
        exact
          (ENat.le_sub_of_add_le_right
            (ENat.natCast_ne_top (clusterSize j)) hadd).trans
              (trace.step j hj))
      hheight (Nat.zero_le clusterCount)
  simpa only [separatedClusterPrefixSize, Finset.sum_range_zero, add_zero]
    using hzero

/-! ## Exact paper-style quantifiers on the separated restriction -/

/-- The canonical increasing enumeration of an infinite set tends from
`atTop` to that set's restricted natural tail. -/
theorem tendsto_nth_restrictedAtTop
    {s : Set ℕ} (hs : s.Infinite) :
    Tendsto (Nat.nth (fun n => n ∈ s)) atTop (restrictedAtTop s) := by
  let p : ℕ → Prop := fun n => n ∈ s
  have hp : (Set.ofPred p).Infinite := by
    change s.Infinite
    exact hs
  rw [restrictedAtTop]
  apply tendsto_inf.mpr
  refine ⟨(Nat.nth_strictMono hp).tendsto_atTop, ?_⟩
  apply tendsto_principal.mpr
  filter_upwards [] with k
  simpa only [p] using Nat.nth_mem_of_infinite hp k

/-- Any convergence statement on an infinite restricted tail can therefore
be fed to an `atTop` theorem after composing with its canonical
enumeration. -/
theorem Tendsto.comp_nth_restrictedAtTop
    {Y : Type v} {s : Set ℕ} (hs : s.Infinite)
    {f : ℕ → Y} {l : Filter Y} (hf : Tendsto f (restrictedAtTop s) l) :
    Tendsto (fun k => f (Nat.nth (fun n => n ∈ s) k)) atTop l :=
  hf.comp (tendsto_nth_restrictedAtTop hs)

/-- On an infinite set of natural numbers, eventual truth on the restricted
tail is equivalent to eventual truth after composition with the canonical
increasing enumeration of that set.  This transports all hypotheses of an
`atTop` theorem, not only its final lower-bound conclusion. -/
theorem eventually_restrictedAtTop_iff_eventually_nth
    {s : Set ℕ} (hs : s.Infinite) {q : ℕ → Prop} :
    (∀ᶠ n in restrictedAtTop s, q n) ↔
      ∀ᶠ k in atTop, q (Nat.nth (fun n => n ∈ s) k) := by
  let p : ℕ → Prop := fun n => n ∈ s
  have hp : (Set.ofPred p).Infinite := by
    change s.Infinite
    exact hs
  constructor
  · intro hq
    rw [eventually_restrictedAtTop_iff_exists] at hq
    obtain ⟨n₀, hn₀⟩ := hq
    have ht : Tendsto (Nat.nth p) atTop atTop :=
      (Nat.nth_strictMono hp).tendsto_atTop
    have hlarge : ∀ᶠ k in atTop, n₀ ≤ Nat.nth p k :=
      ht.eventually (eventually_ge_atTop n₀)
    filter_upwards [hlarge] with k hk
    apply hn₀ (Nat.nth p k) hk
    simpa only [p] using Nat.nth_mem_of_infinite hp k
  · intro hq
    rw [eventually_atTop] at hq
    obtain ⟨k₀, hk₀⟩ := hq
    rw [eventually_restrictedAtTop_iff_exists]
    refine ⟨Nat.nth p k₀, ?_⟩
    intro n hn hns
    have hnrange : n ∈ Set.range (Nat.nth p) := by
      rw [Nat.range_nth_of_infinite hp]
      change p n
      exact hns
    obtain ⟨k, rfl⟩ := hnrange
    exact hk₀ k ((Nat.nth_le_nth hp).mp hn)

/-- A finite restricting set gives the bottom filter, so every finite-family
lower bound is vacuously true there.  This is the finite branch which the
paper's statement intentionally permits. -/
theorem hasInversePowerLowerBound_restrictedAtTop_of_finite
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {s : Set ℕ} (hs : s.Finite) (R : ℕ → ℝ) (f : ι → ℕ → ℝ) :
    HasInversePowerLowerBound (restrictedAtTop s) R f := by
  refine ⟨1, zero_lt_one, 0, ?_⟩
  rw [restrictedAtTop_eq_bot_iff.mpr hs]
  simp

/-- Pull an `atTop` lower bound along the canonical increasing enumeration
of an infinite set back to the corresponding restricted natural tail.

This is the precise bridge needed because the strongest currently
maintained real quantitative-transfer theorem is stated on `atTop`, while
the separated-clusters conclusion uses `restrictedAtTop`. -/
theorem hasInversePowerLowerBound_restrictedAtTop_of_nth
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {s : Set ℕ} (hs : s.Infinite) {R : ℕ → ℝ} {f : ι → ℕ → ℝ}
    (hcomp : HasInversePowerLowerBound atTop
      (fun k => R (Nat.nth (fun n => n ∈ s) k))
      (fun i k => f i (Nat.nth (fun n => n ∈ s) k))) :
    HasInversePowerLowerBound (restrictedAtTop s) R f := by
  obtain ⟨c, hc, M, hbound⟩ := hcomp
  refine ⟨c, hc, M, ?_⟩
  apply (eventually_restrictedAtTop_iff_eventually_nth hs).mpr
  simpa only [finiteFamilyMaxAbs] using hbound

/-- Uniform wrapper for the preceding two cases.  A caller needs to run the
existing `atTop` transfer theorem only when the restricting set is infinite;
if it is finite, the paper's eventual conclusion follows automatically. -/
theorem hasInversePowerLowerBound_restrictedAtTop_of_nth_if_infinite
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {s : Set ℕ} {R : ℕ → ℝ} {f : ι → ℕ → ℝ}
    (hcomp : ∀ hs : s.Infinite,
      HasInversePowerLowerBound atTop
        (fun k => R (Nat.nth (fun n => n ∈ s) k))
        (fun i k => f i (Nat.nth (fun n => n ∈ s) k))) :
    HasInversePowerLowerBound (restrictedAtTop s) R f := by
  rcases s.finite_or_infinite with hs | hs
  · exact hasInversePowerLowerBound_restrictedAtTop_of_finite hs R f
  · exact hasInversePowerLowerBound_restrictedAtTop_of_nth hs (hcomp hs)

/-- Filter form and threshold form of the finite-family lower bound agree on
the paper's set `Λ ∩ Γ N`.  This remains true when that set is finite; in
that case both eventual formulations are vacuous past its last element. -/
theorem hasInversePowerLowerBound_separatedRestriction_iff
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ}
    {R : ℕ → ℝ} {f : ι → ℕ → ℝ} :
    HasInversePowerLowerBound (separatedRestriction Λ Γ N) R f ↔
      ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, ∃ n₀ : ℕ,
        ∀ n, n₀ ≤ n → n ∈ Λ ∩ Γ N →
          c / (R n) ^ M ≤ finiteFamilyMaxAbs f n := by
  constructor
  · rintro ⟨c, hc, M, hbound⟩
    rw [eventually_separatedRestriction_iff, eventually_atTop] at hbound
    exact ⟨c, hc, M, hbound⟩
  · rintro ⟨c, hc, M, n₀, hbound⟩
    refine ⟨c, hc, M, ?_⟩
    rw [eventually_separatedRestriction_iff, eventually_atTop]
    exact ⟨n₀, hbound⟩

/-- The lower-bound conclusion with the quantifier order of
`prop:separated`: `Λ` and `N` are chosen before the arbitrary generating
data.  The data may encode a fixed finite generating list together with all
representative choices made for that list. -/
def SeparatedClustersLowerBoundConclusion
    (Data : Type u) (Γ : ℕ → Set ℕ)
    (generatorCount : Data → ℕ → ℕ)
    (R : ℕ → ℝ)
    (value : (data : Data) → (j : ℕ) →
      Fin (generatorCount data j + 1) → ℕ → ℝ) : Prop :=
  ∃ Λ : Set ℕ, Λ.Infinite ∧ ∃ N : ℕ, ∀ data : Data,
    HasInversePowerLowerBound (separatedRestriction Λ Γ N)
      R (value data 0)

/-- Literal threshold version of `SeparatedClustersLowerBoundConclusion`.
It displays all constants occurring in the paper. -/
def SeparatedClustersThresholdConclusion
    (Data : Type u) (Γ : ℕ → Set ℕ)
    (generatorCount : Data → ℕ → ℕ)
    (R : ℕ → ℝ)
    (value : (data : Data) → (j : ℕ) →
      Fin (generatorCount data j + 1) → ℕ → ℝ) : Prop :=
  ∃ Λ : Set ℕ, Λ.Infinite ∧ ∃ N : ℕ, ∀ data : Data,
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n → n ∈ Λ ∩ Γ N →
        c / (R n) ^ M ≤
          finiteFamilyMaxAbs (value data 0) n

/-- The filter packaging preserves the exact existential/universal order of
the proposition. -/
theorem separatedClustersLowerBoundConclusion_iff_threshold
    {Data : Type u} {Γ : ℕ → Set ℕ}
    {generatorCount : Data → ℕ → ℕ}
    {R : ℕ → ℝ}
    {value : (data : Data) → (j : ℕ) →
      Fin (generatorCount data j + 1) → ℕ → ℝ} :
    SeparatedClustersLowerBoundConclusion Data Γ generatorCount R value ↔
      SeparatedClustersThresholdConclusion Data Γ generatorCount R value := by
  constructor
  · rintro ⟨Λ, hΛ, N, hbound⟩
    refine ⟨Λ, hΛ, N, ?_⟩
    intro data
    exact hasInversePowerLowerBound_separatedRestriction_iff.mp (hbound data)
  · rintro ⟨Λ, hΛ, N, hbound⟩
    refine ⟨Λ, hΛ, N, ?_⟩
    intro data
    exact hasInversePowerLowerBound_separatedRestriction_iff.mpr (hbound data)

/-- End-to-end finite assembly after the analytic one-cluster steps have
been verified.  A single infinite `Λ` and integer `N` are shared by every
choice of generating data, exactly as required in `prop:separated`. -/
theorem separatedClustersLowerBoundConclusion_of_backwardTraces
    {Data : Type u} {Γ : ℕ → Set ℕ}
    {generatorCount : Data → ℕ → ℕ}
    {stageScale : Data → ℕ → ℕ → ℝ}
    {R : ℕ → ℝ}
    {value : (data : Data) → (j : ℕ) →
      Fin (generatorCount data j + 1) → ℕ → ℝ}
    (clusterCount : Data → ℕ)
    (Λ : Set ℕ) (hΛ : Λ.Infinite) (N : ℕ)
    (initialScale : ∀ data : Data, stageScale data 0 = R)
    (trace : ∀ data : Data,
      SeparatedClustersBackwardTrace (separatedRestriction Λ Γ N)
        (clusterCount data) (generatorCount data) (stageScale data) (value data))
    (terminal : ∀ data : Data,
      HasInversePowerLowerBound (separatedRestriction Λ Γ N)
        (stageScale data (clusterCount data))
        (value data (clusterCount data))) :
    SeparatedClustersLowerBoundConclusion Data Γ generatorCount R value := by
  refine ⟨Λ, hΛ, N, ?_⟩
  intro data
  simpa only [initialScale data] using
    (trace data).initial_of_terminal (terminal data)

end AbelFormalization
