import AbelFormalization.IndividualCentralIdealStep
import AbelFormalization.OrderedClusterBalancingSelection
import AbelFormalization.OrderedClusterPrefixAlgebraicStep

/-!
# Individual preprocessing of one ordered cluster

Before the simultaneous central operation on an ordered cluster, the
balancing argument performs a fixed list of one-block central operations.
This module realizes that list in the actual ordered-prefix polynomial ring.

The balancing indices use the successor presentation
`Fin (orderedClusterTailSize c + 1)`, whereas the canonical prefix curry uses
`Fin (orderedCluster c).card`.  We retain the exact equivalence between these
types and conjugate the fixed final order across it.  Consequently the final
curried ideal has precisely the input type of
`ClusterAlgebraicReductionCertificate`, with position `i` representing the
original active block at `finalOrder i`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

section ActiveCoordinates

/-- The balancing enumeration, transported to the active coordinate type
used by the canonical ordered-prefix curry. -/
def orderedClusterBalancingToActiveEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    Fin (data.orderedClusterTailSize c + 1) ≃
      Fin (data.orderedCluster c).card :=
  finCongr (data.orderedClusterTailSize_add_one c)

/-- A balancing index as the corresponding literal block of the
`(c+1)`-prefix ring. -/
def orderedClusterBalancingPrefixBlock
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.OrderedClusterPrefixBlock (c.val + 1) :=
  (data.orderedClusterPrefixSuccEquiv c).symm
    (Sum.inl (data.orderedClusterBalancingToActiveEquiv c i))

@[simp]
theorem orderedClusterBalancingPrefixBlock_split
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.orderedClusterPrefixSuccEquiv c
        (data.orderedClusterBalancingPrefixBlock c i) =
      Sum.inl (data.orderedClusterBalancingToActiveEquiv c i) := by
  exact (data.orderedClusterPrefixSuccEquiv c).apply_symm_apply _

@[simp]
theorem orderedClusterBalancingPrefixBlock_val
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    (data.orderedClusterBalancingPrefixBlock c i).1 =
      data.orderedClusterEnumeration c i :=
  rfl

/-- The fixed decrement list, now typed by actual blocks of the active
ordered-prefix ring. -/
def orderedClusterPrefixIndividualSteps
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))) :
    List (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  fixedSteps.map (data.orderedClusterBalancingPrefixBlock c)

/-- In canonical active coordinates, a final position is sent to the block
which the balancing plan places in that position. -/
def orderedClusterFinalPositionEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1))) :
    Equiv.Perm (Fin (data.orderedCluster c).card) :=
  ((data.orderedClusterBalancingToActiveEquiv c).symm.trans finalOrder).trans
    (data.orderedClusterBalancingToActiveEquiv c)

@[simp]
theorem orderedClusterFinalPositionEquiv_apply
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.orderedClusterFinalPositionEquiv c finalOrder
        (data.orderedClusterBalancingToActiveEquiv c i) =
      data.orderedClusterBalancingToActiveEquiv c (finalOrder i) := by
  simp [orderedClusterFinalPositionEquiv]

@[simp]
theorem orderedClusterFinalPositionEquiv_symm_apply
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    (data.orderedClusterFinalPositionEquiv c finalOrder).symm
        (data.orderedClusterBalancingToActiveEquiv c (finalOrder i)) =
      data.orderedClusterBalancingToActiveEquiv c i := by
  apply (data.orderedClusterFinalPositionEquiv c finalOrder).injective
  simp

/-- Rename canonical active coordinates to final-position coordinates.  The
inverse is used because `orderedClusterFinalPositionEquiv` enumerates the old
block occupying each new position. -/
def orderedClusterFinalOrderAlgEquiv
    (A : Type u) [CommSemiring A]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1))) :
    MvPolynomial
        (ClusterOperationSymbol (Fin (data.orderedCluster c).card)
          (terminalTotalDerivativeCount (fun _ ↦ higher))) A ≃ₐ[A]
      MvPolynomial
        (ClusterOperationSymbol (Fin (data.orderedCluster c).card)
          (terminalTotalDerivativeCount (fun _ ↦ higher))) A :=
  clusterOperationRenameAlgEquiv A
    (data.orderedClusterFinalPositionEquiv c finalOrder).symm
    (terminalTotalDerivativeCount (fun _ ↦ higher))
    (terminalTotalDerivativeCount (fun _ ↦ higher)) (fun _ ↦ rfl)

@[simp]
theorem orderedClusterFinalOrderAlgEquiv_X_q
    (A : Type u) [CommSemiring A]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.orderedClusterFinalOrderAlgEquiv A higher c finalOrder
        (MvPolynomial.X (Sum.inl
          (data.orderedClusterBalancingToActiveEquiv c (finalOrder i)))) =
      MvPolynomial.X (Sum.inl
        (data.orderedClusterBalancingToActiveEquiv c i)) := by
  simp [orderedClusterFinalOrderAlgEquiv,
    clusterOperationRenameAlgEquiv, clusterOperationSymbolEquiv]

@[simp]
theorem orderedClusterFinalOrderAlgEquiv_X_derivative
    (A : Type u) [CommSemiring A]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1))
    (r : Fin (higher + 1)) :
    data.orderedClusterFinalOrderAlgEquiv A higher c finalOrder
        (MvPolynomial.X (Sum.inr (Sum.inl
          ⟨data.orderedClusterBalancingToActiveEquiv c (finalOrder i), r⟩))) =
      MvPolynomial.X (Sum.inr (Sum.inl
        ⟨data.orderedClusterBalancingToActiveEquiv c i, r⟩)) := by
  simp [orderedClusterFinalOrderAlgEquiv,
    clusterOperationRenameAlgEquiv, clusterOperationSymbolEquiv]
  congr 3
  apply Sigma.ext
  · exact data.orderedClusterFinalPositionEquiv_symm_apply c finalOrder i
  · rfl

@[simp]
theorem orderedClusterFinalOrderAlgEquiv_X_time
    (A : Type u) [CommSemiring A]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.orderedClusterFinalOrderAlgEquiv A higher c finalOrder
        (MvPolynomial.X (Sum.inr (Sum.inr
          (data.orderedClusterBalancingToActiveEquiv c (finalOrder i))))) =
      MvPolynomial.X (Sum.inr (Sum.inr
        (data.orderedClusterBalancingToActiveEquiv c i))) := by
  simp [orderedClusterFinalOrderAlgEquiv,
    clusterOperationRenameAlgEquiv, clusterOperationSymbolEquiv]

end ActiveCoordinates

section Ideals

/-- One balancing decrement at its literal active block in the
`(c+1)`-prefix ring. -/
def orderedClusterIndividualCentralIdealStep
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)) := by
  classical
  exact individualCentralIdealStep R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterBalancingPrefixBlock c i) I

/-- A single literal ordered-cluster decrement does not decrease height. -/
theorem orderedClusterIndividualCentralIdealStep_height_le
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    I.height ≤
      (data.orderedClusterIndividualCentralIdealStep
        R higher c i I).height := by
  classical
  exact individualCentralIdealStep_height_le R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterBalancingPrefixBlock c i) I

/-- The prefix-stage ideal after all fixed individual balancing decrements
for the active cluster have been performed in chronological order. -/
def orderedClusterIndividuallyPreprocessedIdeal
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)) :=
  by
    classical
    exact individualCentralIdealSteps R
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1))
      (data.orderedClusterPrefixIndividualSteps c fixedSteps) I

@[simp]
theorem orderedClusterIndividuallyPreprocessedIdeal_nil
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    data.orderedClusterIndividuallyPreprocessedIdeal
      R higher c [] I = I := by
  rfl

@[simp]
theorem orderedClusterIndividuallyPreprocessedIdeal_cons
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1))
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    data.orderedClusterIndividuallyPreprocessedIdeal
        R higher c (i :: fixedSteps) I =
      data.orderedClusterIndividuallyPreprocessedIdeal R higher c fixedSteps
        (data.orderedClusterIndividualCentralIdealStep
          R higher c i I) := by
  rfl

/-- Individual preprocessing never decreases the height of the prefix-stage
ideal. -/
theorem orderedClusterIndividuallyPreprocessedIdeal_height_le
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    I.height ≤
      (data.orderedClusterIndividuallyPreprocessedIdeal
        R higher c fixedSteps I).height := by
  classical
  exact individualCentralIdealSteps_height_le R
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (data.orderedClusterPrefixIndividualSteps c fixedSteps) I

/-- Curry the individually preprocessed prefix and then rename canonical
active coordinates into final balancing positions. -/
def orderedClusterPreprocessedCurriedIdeal
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    Ideal
      (MvPolynomial
        (ClusterOperationSymbol (Fin (data.orderedCluster c).card)
          (terminalTotalDerivativeCount (fun _ ↦ higher)))
        (data.OrderedClusterPrefixRing R higher c.val)) :=
  (data.orderedClusterPrefixCurriedIdeal R higher c
      (data.orderedClusterIndividuallyPreprocessedIdeal
        R higher c fixedSteps I)).map
    (data.orderedClusterFinalOrderAlgEquiv
      (data.OrderedClusterPrefixRing R higher c.val)
      higher c finalOrder).toRingHom

/-- Currying and final-order relabeling preserve exactly the height reached
after the individual decrements. -/
theorem orderedClusterPreprocessedCurriedIdeal_height
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    (data.orderedClusterPreprocessedCurriedIdeal
        R higher c fixedSteps finalOrder I).height =
      (data.orderedClusterIndividuallyPreprocessedIdeal
        R higher c fixedSteps I).height := by
  let J := data.orderedClusterIndividuallyPreprocessedIdeal
    R higher c fixedSteps I
  have hrename :
      ((data.orderedClusterPrefixCurriedIdeal R higher c J).map
        (data.orderedClusterFinalOrderAlgEquiv
          (data.OrderedClusterPrefixRing R higher c.val)
          higher c finalOrder).toRingHom).height =
        (data.orderedClusterPrefixCurriedIdeal R higher c J).height := by
    exact
      (data.orderedClusterFinalOrderAlgEquiv
          (data.OrderedClusterPrefixRing R higher c.val)
          higher c finalOrder).toRingEquiv.height_map
        (data.orderedClusterPrefixCurriedIdeal R higher c J)
  change ((data.orderedClusterPrefixCurriedIdeal R higher c J).map
      (data.orderedClusterFinalOrderAlgEquiv
        (data.OrderedClusterPrefixRing R higher c.val)
        higher c finalOrder).toRingHom).height = J.height
  exact hrename.trans
    (data.orderedClusterPrefixCurriedIdeal_height R higher c J)

/-- The complete preprocessing, including final-order relabeling, never
decreases the height of the incoming prefix-stage ideal. -/
theorem orderedClusterPreprocessedCurriedIdeal_height_le
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    I.height ≤
      (data.orderedClusterPreprocessedCurriedIdeal
        R higher c fixedSteps finalOrder I).height := by
  calc
    I.height ≤
        (data.orderedClusterIndividuallyPreprocessedIdeal
          R higher c fixedSteps I).height :=
      data.orderedClusterIndividuallyPreprocessedIdeal_height_le
        R higher c fixedSteps I
    _ = (data.orderedClusterPreprocessedCurriedIdeal
          R higher c fixedSteps finalOrder I).height :=
      (data.orderedClusterPreprocessedCurriedIdeal_height
        R higher c fixedSteps finalOrder I).symm

/-- The preprocessed and final-order-relabeled ideal is a literal admissible
input for the simultaneous algebraic reduction of the active cluster. -/
theorem nonempty_orderedClusterPreprocessedAlgebraicReductionCertificate
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    {krullDim : ℕ}
    [Algebra ℚ (data.OrderedClusterPrefixRing R higher c.val)]
    [IsNoetherianRing (data.OrderedClusterPrefixRing R higher c.val)]
    [Ring.KrullDimLE krullDim
      (data.OrderedClusterPrefixRing R higher c.val)] :
    Nonempty
      (ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher c.val)
        (data.orderedCluster c).card (fun _ ↦ higher)
        (data.orderedClusterPreprocessedCurriedIdeal
          R higher c fixedSteps finalOrder I)) := by
  exact exists_clusterAlgebraicReductionCertificate
    (krullDim := krullDim) (fun _ ↦ higher)
    (MonomialOrder.lex : MonomialOrder
      (Fin (clusterTerminalReindexCard (fun _ :
        Fin (data.orderedCluster c).card ↦ higher))))
    (clusterTerminalFiniteReindex (fun _ :
      Fin (data.orderedCluster c).card ↦ higher))
    (data.orderedClusterPreprocessedCurriedIdeal
      R higher c fixedSteps finalOrder I)

/-- Height present before balancing remains available to the usual
cluster-size contraction estimate after simultaneous reduction. -/
theorem orderedClusterPreprocessedAlgebraicReduction_preserves_baseHeight
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (finalOrder : Equiv.Perm
      (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher c.val)
      (data.orderedCluster c).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal
        R higher c fixedSteps finalOrder I))
    (q : ℕ)
    (hheight : (q : ENat) + ((data.orderedCluster c).card : ENat) ≤
      I.height) :
    (q : ENat) ≤ certificate.terminalized.coefficientIdeal.height := by
  apply clusterAlgebraicReduction_preserves_baseHeight certificate
  exact hheight.trans
    (data.orderedClusterPreprocessedCurriedIdeal_height_le
      R higher c fixedSteps finalOrder I)

end Ideals

end RepresentativeClusterSubsequence
end AbelFormalization
