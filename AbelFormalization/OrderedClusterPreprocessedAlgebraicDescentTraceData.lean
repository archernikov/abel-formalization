import AbelFormalization.OrderedClusterPreprocessedTransferTraceData
import AbelFormalization.FiniteFamilyFlattening

/-!
# A flattened transfer trace for the full preprocessed cluster descent

A completed `OrderedClusterPreprocessedAlgebraicDescent` contains one
dependent algebraic stage for every ordered cluster.  The coefficient ring of
stage `c` is the prefix ring at `c`, so transfer certificates from different
clusters cannot be put in one ordinary homogeneous family.

This module first chooses `FullTransferTraceData` at every dependent stage.
It then uses `FiniteFamilyFlattening.ClusterTransferOperation` to enumerate,
in order, every individual operation, the first simultaneous operation, and
all extra retained operations.  The flattened view remains a dependent Sigma,
so every operation retains its literal coefficient ring and certificate type.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

open FiniteFamilyFlattening

universe u

namespace OrderedClusterPreprocessedAlgebraicDescent

noncomputable local instance orderedClusterTracePrefixBlockDecidableEq
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time} {k : ℕ} :
    DecidableEq (data.OrderedClusterPrefixBlock k) :=
  Classical.decEq _

/-- The dependent algebraic stage belonging to an ordered-cluster index. -/
abbrev clusterStage
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) :=
  descent.stageAt c.val c.isLt

/-- A simultaneous choice of the complete transfer data at every dependent
cluster stage of a completed descent. -/
structure FullTransferTraceData
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal) where
  stage : (c : Fin data.orderedClusterCount) →
    (descent.clusterStage c).FullTransferTraceData

/-- Noetherianity chooses the complete local transfer data simultaneously at
every cluster of a completed descent. -/
theorem nonempty_fullTransferTraceData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    [∀ j, IsNoetherianRing (data.OrderedClusterPrefixRing R higher j)] :
    Nonempty descent.FullTransferTraceData := by
  classical
  exact ⟨{
    stage := fun c ↦ Classical.choice
      (descent.clusterStage c).nonempty_fullTransferTraceData
  }⟩

/-- The number of individual operations at cluster `c`.  This is stated using
the actual literal-prefix block list consumed by the selected trace data. -/
def individualTransferCount
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (_descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) : ℕ :=
  (data.orderedClusterPrefixIndividualSteps c (fixedSteps c)).length

/-- The number of extra retained simultaneous operations at cluster `c`. -/
def extraRetainedTransferCount
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) : ℕ :=
  (descent.clusterStage c).certificate.terminalized.extraSteps

/-- The local chronological length is the generic three-phase cluster transfer
length: every individual step, one first simultaneous step, then the extra
retained steps. -/
abbrev transferLength
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) : ℕ :=
  clusterTransferLength descent.individualTransferCount
    descent.extraRetainedTransferCount c

/-- The total number of transfer operations in the completed descent. -/
abbrev totalTransferCount
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal) : ℕ :=
  totalClusterTransferCount descent.individualTransferCount
    descent.extraRetainedTransferCount

/-- The local three-phase operation type at a cluster. -/
abbrev TransferOperation
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) :=
  ClusterTransferOperation (descent.individualTransferCount c)
    (descent.extraRetainedTransferCount c)

/-- The canonical flattening equivalence for every transfer operation in the
completed descent. -/
def transferEquiv
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal) :
    Fin descent.totalTransferCount ≃ Σ c, descent.TransferOperation c :=
  orderedClusterTransferEquiv descent.individualTransferCount
    descent.extraRetainedTransferCount

/-- Insert a named dependent local operation into the flattened trace. -/
def transferIndex
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) (operation : descent.TransferOperation c) :
    Fin descent.totalTransferCount :=
  clusterTransferIndex descent.individualTransferCount
    descent.extraRetainedTransferCount c operation

/-- Locate a global index as its dependent cluster and three-phase operation. -/
def operationAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (j : Fin descent.totalTransferCount) :
    Σ c, descent.TransferOperation c :=
  descent.transferEquiv j

@[simp]
theorem operationAt_transferIndex
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) (operation : descent.TransferOperation c) :
    descent.operationAt (descent.transferIndex c operation) = ⟨c, operation⟩ := by
  exact orderedClusterTransferEquiv_clusterTransferIndex
    descent.individualTransferCount descent.extraRetainedTransferCount c operation

@[simp]
theorem operationAt_individual
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.individualTransferCount c)) :
    descent.operationAt (descent.transferIndex c (.individual i)) =
      ⟨c, .individual i⟩ :=
  descent.operationAt_transferIndex c (.individual i)

@[simp]
theorem operationAt_firstSimultaneous
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) :
    descent.operationAt (descent.transferIndex c .firstSimultaneous) =
      ⟨c, .firstSimultaneous⟩ :=
  descent.operationAt_transferIndex c .firstSimultaneous

@[simp]
theorem operationAt_extraRetained
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.extraRetainedTransferCount c)) :
    descent.operationAt (descent.transferIndex c (.extraRetained i)) =
      ⟨c, .extraRetained i⟩ :=
  descent.operationAt_transferIndex c (.extraRetained i)

/-- The exact local length of a cluster, exposing all three phases. -/
@[simp]
theorem transferLength_eq
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) :
    descent.transferLength c = descent.individualTransferCount c + 1 +
      descent.extraRetainedTransferCount c := rfl

/-- The exact total count is the sum of the three-phase local lengths. -/
theorem totalTransferCount_eq_sum
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal) :
    descent.totalTransferCount =
      ∑ c, (descent.individualTransferCount c + 1 +
        descent.extraRetainedTransferCount c) := rfl

/-- The exact flattened index of an individual operation. -/
@[simp]
theorem transferIndex_individual_val
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.individualTransferCount c)) :
    (descent.transferIndex c (.individual i) : ℕ) =
      prefixOffset descent.transferLength c.castSucc + i := by
  exact clusterTransferIndex_individual_val descent.individualTransferCount
    descent.extraRetainedTransferCount c i

/-- The first simultaneous operation follows every individual operation in
its cluster. -/
@[simp]
theorem transferIndex_firstSimultaneous_val
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount) :
    (descent.transferIndex c .firstSimultaneous : ℕ) =
      prefixOffset descent.transferLength c.castSucc +
        descent.individualTransferCount c := by
  exact clusterTransferIndex_firstSimultaneous_val
    descent.individualTransferCount descent.extraRetainedTransferCount c

/-- Extra retained operation `i` follows the first simultaneous operation. -/
@[simp]
theorem transferIndex_extraRetained_val
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.extraRetainedTransferCount c)) :
    (descent.transferIndex c (.extraRetained i) : ℕ) =
      prefixOffset descent.transferLength c.castSucc +
        descent.individualTransferCount c + 1 + i := by
  exact clusterTransferIndex_extraRetained_val
    descent.individualTransferCount descent.extraRetainedTransferCount c i

namespace FullTransferTraceData

/-- The chosen individual transfer datum at its literal dependent prefix-ring
stage. -/
def individualTransferAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.individualTransferCount c)) :
    IndividualCentralTransferData R
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      ((data.orderedClusterPrefixIndividualSteps c
        (fixedSteps c)).get i)
      (individualCentralIdealBefore R
        (data.orderedClusterPrefixConstantDerivativeCount
          (higher + 1) (c.val + 1))
        (data.orderedClusterPrefixIndividualSteps c (fixedSteps c))
        (descent.clusterStage c).preprocessingInput i) :=
  (trace.stage c).individual.transferData i

/-- The displayed generators and exact identities selected for an individual
operation, still over its literal dependent coefficient ring. -/
def individualDisplayedAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.individualTransferCount c)) :
    IndividualCentralTransferData.DisplayedData R
      (trace.individualTransferAt c i) :=
  (trace.stage c).individualDisplayed.displayed i

/-- The chosen simultaneous quantitative-transfer certificate at a full
central index.  Its coefficient ring is explicitly the prefix ring at `c`. -/
def simultaneousTransferAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (r : Fin (descent.extraRetainedTransferCount c + 1)) :
    CentralQuantitativeTransferCertificate
      (data.OrderedClusterPrefixRing R higher c.val)
      (Fin (data.orderedCluster c).card) (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ ↦ higher))
      (data.orderedCluster c).card
      (centralTransferShear (terminalTotalDerivativeCount (fun _ ↦ higher)))
      ((descent.clusterStage c).certificate.centralTransferInput r) :=
  (trace.stage c).simultaneous.transferCertificate r

/-- The displayed generators and identities chosen at a full simultaneous
index. -/
def simultaneousDisplayedAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (r : Fin (descent.extraRetainedTransferCount c + 1)) :
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
      (trace.stage c).simultaneous r :=
  (trace.stage c).simultaneousDisplayed r

/-- The first simultaneous transfer certificate at cluster `c`. -/
def firstSimultaneousTransferAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount) :=
  trace.simultaneousTransferAt c
    (descent.clusterStage c).certificate.firstCentralStepIndex

/-- The displayed data for the first simultaneous operation at cluster `c`. -/
def firstSimultaneousDisplayedAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount) :=
  trace.simultaneousDisplayedAt c
    (descent.clusterStage c).certificate.firstCentralStepIndex

/-- Extra retained transfer `i` is simultaneous index `i + 1`. -/
def extraRetainedTransferAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.extraRetainedTransferCount c)) :=
  trace.simultaneousTransferAt c i.succ

/-- The displayed data for extra retained transfer `i`. -/
def extraRetainedDisplayedAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.extraRetainedTransferCount c)) :=
  trace.simultaneousDisplayedAt c i.succ

/-- A dependent local view packages the displayed datum belonging to a named
operation.  The individual and simultaneous constructors retain their
different coefficient rings and certificate types. -/
inductive OperationView
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount) : descent.TransferOperation c → Type (u + 1)
  | individual (i : Fin (descent.individualTransferCount c))
      (displayed : IndividualCentralTransferData.DisplayedData R
        (trace.individualTransferAt c i)) :
      OperationView trace c (.individual i)
  | firstSimultaneous
      (displayed : ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
        (trace.stage c).simultaneous
        (descent.clusterStage c).certificate.firstCentralStepIndex) :
      OperationView trace c .firstSimultaneous
  | extraRetained (i : Fin (descent.extraRetainedTransferCount c))
      (displayed : ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData
        (trace.stage c).simultaneous i.succ) :
      OperationView trace c (.extraRetained i)

/-- Construct the exact dependent view of a named local operation. -/
def localOperationView
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (operation : descent.TransferOperation c) :
    trace.OperationView c operation := by
  cases operation with
  | individual i =>
      exact .individual i (trace.individualDisplayedAt c i)
  | firstSimultaneous =>
      exact .firstSimultaneous (trace.firstSimultaneousDisplayedAt c)
  | extraRetained i =>
      exact .extraRetained i (trace.extraRetainedDisplayedAt c i)

/-- The flattened dependent Sigma view of operation `j`. -/
def operationViewAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (j : Fin descent.totalTransferCount) :
    Σ c, Σ operation : descent.TransferOperation c,
      trace.OperationView c operation :=
  let located := descent.operationAt j
  ⟨located.1, located.2, trace.localOperationView located.1 located.2⟩

@[simp]
theorem operationViewAt_transferIndex
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (operation : descent.TransferOperation c) :
    trace.operationViewAt (descent.transferIndex c operation) =
      ⟨c, operation, trace.localOperationView c operation⟩ := by
  unfold operationViewAt
  rw [descent.operationAt_transferIndex c operation]

@[simp]
theorem operationViewAt_individual
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.individualTransferCount c)) :
    trace.operationViewAt (descent.transferIndex c (.individual i)) =
      ⟨c, .individual i,
        .individual i (trace.individualDisplayedAt c i)⟩ := by
  rw [trace.operationViewAt_transferIndex c (.individual i)]
  rfl

@[simp]
theorem operationViewAt_firstSimultaneous
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount) :
    trace.operationViewAt (descent.transferIndex c .firstSimultaneous) =
      ⟨c, .firstSimultaneous,
        .firstSimultaneous (trace.firstSimultaneousDisplayedAt c)⟩ := by
  rw [trace.operationViewAt_transferIndex c .firstSimultaneous]
  rfl

@[simp]
theorem operationViewAt_extraRetained
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    (c : Fin data.orderedClusterCount)
    (i : Fin (descent.extraRetainedTransferCount c)) :
    trace.operationViewAt (descent.transferIndex c (.extraRetained i)) =
      ⟨c, .extraRetained i,
        .extraRetained i (trace.extraRetainedDisplayedAt c i)⟩ := by
  rw [trace.operationViewAt_transferIndex c (.extraRetained i)]
  rfl

end FullTransferTraceData
end OrderedClusterPreprocessedAlgebraicDescent

end RepresentativeClusterSubsequence
end AbelFormalization
