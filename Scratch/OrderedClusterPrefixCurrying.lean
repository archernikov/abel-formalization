import AbelFormalization.OrderedClusterPrefixBlocks
import AbelFormalization.PaperRankClusterCurrying

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

universe u v w

/-- Reindex every variable in one cluster-operation ring along an
equivalence of its block type. -/
def clusterOperationSymbolEquiv
    {Block : Type v} {Block' : Type w}
    (e : Block ≃ Block') (d : Block → ℕ) (d' : Block' → ℕ)
    (hd : ∀ b, d b = d' (e b)) :
    ClusterOperationSymbol Block d ≃ ClusterOperationSymbol Block' d' :=
  Equiv.sumCongr e
    (Equiv.sumCongr
      (Equiv.sigmaCongr e (fun b ↦ finCongr (hd b))) e)

@[simp]
theorem clusterOperationSymbolEquiv_apply_q
    {Block : Type v} {Block' : Type w}
    (e : Block ≃ Block') (d : Block → ℕ) (d' : Block' → ℕ)
    (hd : ∀ b, d b = d' (e b)) (b : Block) :
    clusterOperationSymbolEquiv e d d' hd (Sum.inl b) =
      Sum.inl (e b) :=
  rfl

@[simp]
theorem clusterOperationSymbolEquiv_apply_derivative
    {Block : Type v} {Block' : Type w}
    (e : Block ≃ Block') (d : Block → ℕ) (d' : Block' → ℕ)
    (hd : ∀ b, d b = d' (e b)) (b : Block) (r : Fin (d b)) :
    clusterOperationSymbolEquiv e d d' hd
        (Sum.inr (Sum.inl ⟨b, r⟩)) =
      Sum.inr (Sum.inl ⟨e b, finCongr (hd b) r⟩) :=
  rfl

@[simp]
theorem clusterOperationSymbolEquiv_apply_time
    {Block : Type v} {Block' : Type w}
    (e : Block ≃ Block') (d : Block → ℕ) (d' : Block' → ℕ)
    (hd : ∀ b, d b = d' (e b)) (b : Block) :
    clusterOperationSymbolEquiv e d d' hd
        (Sum.inr (Sum.inr b)) =
      Sum.inr (Sum.inr (e b)) :=
  rfl

/-- Polynomial reindexing induced by a block equivalence. -/
def clusterOperationRenameAlgEquiv
    (R : Type u) [CommSemiring R]
    {Block : Type v} {Block' : Type w}
    (e : Block ≃ Block') (d : Block → ℕ) (d' : Block' → ℕ)
    (hd : ∀ b, d b = d' (e b)) :
    MvPolynomial (ClusterOperationSymbol Block d) R ≃ₐ[R]
      MvPolynomial (ClusterOperationSymbol Block' d') R :=
  MvPolynomial.renameEquiv R (clusterOperationSymbolEquiv e d d' hd)

namespace RepresentativeClusterSubsequence

/-- Every block in every Hermite stage has the same retained positive
derivative count. -/
abbrev orderedClusterPrefixConstantDerivativeCount
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (D k : ℕ) :
    data.OrderedClusterPrefixBlock k → ℕ :=
  fun _ ↦ D

/-- Reindex the flat variables in a nonzero ordered-cluster prefix into its
active cluster and its smaller-cluster coefficient prefix. -/
def orderedClusterPrefixOperationEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (D : ℕ) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount D (c.val + 1)) ≃
      SplitClusterBlockSymbol
        (Fin (data.orderedCluster c).card)
        (data.OrderedClusterPrefixBlock c.val)
        (fun _ ↦ D) (fun _ ↦ D) := by
  let e := data.orderedClusterPrefixSuccEquiv c
  apply clusterOperationSymbolEquiv e
    (data.orderedClusterPrefixConstantDerivativeCount D (c.val + 1))
    (Sum.elim (fun _ : Fin (data.orderedCluster c).card ↦ D)
      (fun _ : data.OrderedClusterPrefixBlock c.val ↦ D))
  intro b
  change D = Sum.elim (fun _ : Fin (data.orderedCluster c).card ↦ D)
    (fun _ : data.OrderedClusterPrefixBlock c.val ↦ D) (e b)
  rcases e b with a | b <;> rfl

/-- Curry the active cluster out of a flat polynomial ring on a nonzero
ordered-cluster prefix.  The coefficient ring is exactly the polynomial
ring on the smaller-cluster prefix. -/
def orderedClusterPrefixCurryAlgEquiv
    (R : Type u) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (D : ℕ) :
    MvPolynomial
        (ClusterOperationSymbol
          (data.OrderedClusterPrefixBlock (c.val + 1))
          (data.orderedClusterPrefixConstantDerivativeCount D (c.val + 1))) R
        ≃ₐ[R]
      MvPolynomial
        (ClusterOperationSymbol (Fin (data.orderedCluster c).card)
          (fun _ ↦ D))
        (MvPolynomial
          (ClusterOperationSymbol (data.OrderedClusterPrefixBlock c.val)
            (data.orderedClusterPrefixConstantDerivativeCount D c.val)) R) :=
  (MvPolynomial.renameEquiv R
    (data.orderedClusterPrefixOperationEquiv c D)).trans
      (splitClusterCurryAlgEquiv R
        (Fin (data.orderedCluster c).card)
        (data.OrderedClusterPrefixBlock c.val)
        (fun _ ↦ D)
        (data.orderedClusterPrefixConstantDerivativeCount D c.val))

end RepresentativeClusterSubsequence
end AbelFormalization
