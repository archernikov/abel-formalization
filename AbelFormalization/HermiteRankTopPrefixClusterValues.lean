import AbelFormalization.HermiteRankTopPrefixEvaluation
import AbelFormalization.PaperRankFullHermiteValue

/-!
# Concrete Hermite values on ordered-cluster prefixes

The full paper-rank Hermite assignment is first transported to the top
ordered-cluster prefix.  Its free, positive-derivative, and time coordinates
are identified with the existing concrete Hermite values.  Restricting those
values to an arbitrary prefix then gives the active and coefficient
assignments at one ordered-cluster stage.

The final evaluation theorem identifies evaluation of every flat prefix
polynomial with nested coefficient/active evaluation after
`orderedClusterPrefixCurryAlgEquiv`.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The complete Hermite assignment after relabeling the flat blocks by the
full ordered-cluster prefix. -/
def paperRankHermiteTopPrefixValue
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) data.orderedClusterCount) → ℝ :=
  data.paperRankHermiteTopPrefixAssignment S
    (paperRankFullHermiteRetainedValue D representative offset S B F sw)

/-- Forget the ordered-prefix label while converting the stage derivative
count to the equal positive-Hermite coefficient count. -/
def paperRankHermiteTopPrefixToFlatEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) :
    ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock data.orderedClusterCount)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) data.orderedClusterCount) ≃
      ClusterOperationSymbol (Fin m)
        (fun _ => paperRankHermitePositiveDerivativeCount S) :=
  clusterOperationSymbolEquiv data.orderedClusterPrefixTopEquiv.symm
    (data.orderedClusterPrefixConstantDerivativeCount
      (paperRankHermiteHigherCount S + 1) data.orderedClusterCount)
    (fun _ : Fin m => paperRankHermitePositiveDerivativeCount S)
    (fun _ => paperRankHermiteHigherCount_add_one S)

@[simp]
theorem paperRankHermiteTopPrefixValue_free
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (i : Fin m) :
    paperRankHermiteTopPrefixValue data D representative offset S B F sw
        (data.paperRankHermiteTopPrefixSymbolEquiv S (Sum.inl i)) =
      sw.1 i := by
  simp [paperRankHermiteTopPrefixValue, paperRankHermiteTopPrefixAssignment]

@[simp]
theorem paperRankHermiteTopPrefixValue_positiveDerivative
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (i : Fin m)
    (r : Fin (paperRankHermitePositiveDerivativeCount S)) :
    paperRankHermiteTopPrefixValue data D representative offset S B F sw
        (data.paperRankHermiteTopPrefixSymbolEquiv S
          ((paperRankRetainedFlatHermiteEquiv m
            (paperRankHermitePositiveDerivativeCount S)).symm
              (Sum.inr (Sum.inl ⟨i, r⟩)))) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr i) r.succ := by
  simp only [paperRankHermiteTopPrefixValue,
    paperRankHermiteTopPrefixAssignment, Function.comp_apply,
    Equiv.symm_apply_apply]
  unfold paperRankFullHermiteRetainedValue
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem paperRankHermiteTopPrefixValue_time
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (i : Fin m) :
    paperRankHermiteTopPrefixValue data D representative offset S B F sw
        (data.paperRankHermiteTopPrefixSymbolEquiv S
          ((paperRankRetainedFlatHermiteEquiv m
            (paperRankHermitePositiveDerivativeCount S)).symm
              (Sum.inr (Sum.inr i)))) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr i) 0 := by
  simp only [paperRankHermiteTopPrefixValue,
    paperRankHermiteTopPrefixAssignment, Function.comp_apply,
    Equiv.symm_apply_apply]
  unfold paperRankFullHermiteRetainedValue
  rw [Equiv.apply_symm_apply]
  rfl

/-- The top-prefix representative evaluates at the transported complete
Hermite assignment exactly as the original retained representative does. -/
theorem eval_paperRankHermiteTopPrefixRepresentative_fullHermiteValue
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (G : RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ)
    (w : RestrictedBoxSpace p) :
    MvPolynomial.eval
        (paperRankHermiteTopPrefixValue data D representative offset S B F sw)
        (paperRankHermiteTopPrefixRepresentative data S G w) =
      MvPolynomial.eval
        (paperRankFullHermiteRetainedValue D representative offset S B F sw)
        (G w) := by
  rw [paperRankHermiteTopPrefixRepresentative_apply]
  exact eval_paperRankHermiteTopPrefixAlgEquiv ℝ data S
    (paperRankFullHermiteRetainedValue D representative offset S B F sw)
    (G w)

/-! ## Concrete values on every ordered-cluster prefix -/

/-- Forget a prefix block's proof and view its three operation coordinates in
the original flat Hermite block ring. -/
def paperRankHermitePrefixFlatSymbol
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ)) (k : ℕ) :
    ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) k) →
      ClusterOperationSymbol (Fin m)
        (paperRankHermiteBlockDerivativeCount S (Fin m))
  | Sum.inl b => Sum.inl b.1
  | Sum.inr (Sum.inl ⟨b, r⟩) =>
      Sum.inr (Sum.inl ⟨b.1,
        finCongr (paperRankHermiteHigherCount_add_one S) r⟩)
  | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b.1)

/-- The concrete Hermite assignment on an arbitrary surviving ordered
prefix.  It is the restriction of the all-block coefficient assignment along
the underlying representative indices. -/
def paperRankHermitePrefixValue
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (k : ℕ) :
    ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount S + 1) k) → ℝ :=
  (paperRankHermiteCoefficientBlockValue D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
    B (fun _ => F) sw) ∘ paperRankHermitePrefixFlatSymbol data S k

@[simp]
theorem paperRankHermitePrefixValue_free
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (k : ℕ)
    (b : data.OrderedClusterPrefixBlock k) :
    paperRankHermitePrefixValue data D representative offset S B F sw k
        (Sum.inl b) = sw.1 b.1 := by
  rfl

@[simp]
theorem paperRankHermitePrefixValue_positiveDerivative
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (k : ℕ)
    (b : data.OrderedClusterPrefixBlock k)
    (r : Fin (paperRankHermiteHigherCount S + 1)) :
    paperRankHermitePrefixValue data D representative offset S B F sw k
        (Sum.inr (Sum.inl ⟨b, r⟩)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr b.1)
        (finCongr (paperRankHermiteHigherCount_add_one S) r).succ := by
  rfl

@[simp]
theorem paperRankHermitePrefixValue_time
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (k : ℕ)
    (b : data.OrderedClusterPrefixBlock k) :
    paperRankHermitePrefixValue data D representative offset S B F sw k
        (Sum.inr (Sum.inr b)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr b.1) 0 := by
  rfl

/-! ## Evaluation after splitting one ordered prefix -/

/-- Transport a value assignment on a nonzero ordered prefix through the
canonical split into its active cluster and the smaller prefix. -/
def orderedClusterPrefixSplitAssignment
    {T : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T) :
    SplitClusterBlockSymbol
      (Fin (data.orderedCluster c).card)
      (data.OrderedClusterPrefixBlock c.val)
      (fun _ => d) (fun _ => d) → T :=
  v ∘ (data.orderedClusterPrefixOperationEquiv c d).symm

/-- The active-cluster part of a transported prefix assignment. -/
def orderedClusterPrefixActiveAssignment
    {T : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T) :
    ClusterOperationSymbol (Fin (data.orderedCluster c).card)
      (fun _ => d) → T :=
  fun z => orderedClusterPrefixSplitAssignment data c d v
    ((splitClusterBlockSymbolEquiv
      (Fin (data.orderedCluster c).card)
      (data.OrderedClusterPrefixBlock c.val)
      (fun _ => d) (fun _ => d)).symm (Sum.inl z))

/-- The smaller-prefix coefficient part of a transported prefix assignment. -/
def orderedClusterPrefixCoefficientAssignment
    {T : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T) :
    ClusterOperationSymbol (data.OrderedClusterPrefixBlock c.val)
      (data.orderedClusterPrefixConstantDerivativeCount d c.val) → T :=
  fun z => orderedClusterPrefixSplitAssignment data c d v
    ((splitClusterBlockSymbolEquiv
      (Fin (data.orderedCluster c).card)
      (data.OrderedClusterPrefixBlock c.val)
      (fun _ => d) (fun _ => d)).symm (Sum.inr z))

theorem orderedClusterPrefixSplitAssignment_eq_sum_elim
    {T : Type*}
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (z : SplitClusterBlockSymbol
      (Fin (data.orderedCluster c).card)
      (data.OrderedClusterPrefixBlock c.val)
      (fun _ => d) (fun _ => d)) :
    Sum.elim
        (orderedClusterPrefixActiveAssignment data c d v)
        (orderedClusterPrefixCoefficientAssignment data c d v)
        (splitClusterBlockSymbolEquiv
          (Fin (data.orderedCluster c).card)
          (data.OrderedClusterPrefixBlock c.val)
          (fun _ => d) (fun _ => d) z) =
      orderedClusterPrefixSplitAssignment data c d v z := by
  let e := splitClusterBlockSymbolEquiv
    (Fin (data.orderedCluster c).card)
    (data.OrderedClusterPrefixBlock c.val)
    (fun _ => d) (fun _ => d)
  generalize hz : e z = y
  rcases y with a | b
  · change orderedClusterPrefixSplitAssignment data c d v
      (e.symm (Sum.inl a)) = _
    rw [← hz, e.symm_apply_apply]
  · change orderedClusterPrefixSplitAssignment data c d v
      (e.symm (Sum.inr b)) = _
    rw [← hz, e.symm_apply_apply]

/-- Evaluation of a prefix polynomial is exactly nested evaluation after the
canonical ordered-cluster currying equivalence. -/
theorem eval₂Hom_orderedClusterPrefixCurryAlgEquiv
    {R T : Type*} [CommSemiring R] [CommSemiring T]
    (f : R →+* T)
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (P : MvPolynomial
      (ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1))) R) :
    MvPolynomial.eval₂Hom f v P =
      MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom f
          (orderedClusterPrefixCoefficientAssignment data c d v))
        (orderedClusterPrefixActiveAssignment data c d v)
        (data.orderedClusterPrefixCurryAlgEquiv R c d P) := by
  let e := data.orderedClusterPrefixOperationEquiv c d
  let splitValue := orderedClusterPrefixSplitAssignment data c d v
  let activeValue := orderedClusterPrefixActiveAssignment data c d v
  let coefficientValue :=
    orderedClusterPrefixCoefficientAssignment data c d v
  have hrename :
      MvPolynomial.eval₂Hom f v P =
        MvPolynomial.eval₂Hom f splitValue (MvPolynomial.rename e P) := by
    change MvPolynomial.eval₂ f v P =
      MvPolynomial.eval₂ f splitValue (MvPolynomial.rename e P)
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext z
    simp [splitValue, orderedClusterPrefixSplitAssignment, e]
  have hsplit :
      (fun z => Sum.elim activeValue coefficientValue
        (splitClusterBlockSymbolEquiv
          (Fin (data.orderedCluster c).card)
          (data.OrderedClusterPrefixBlock c.val)
          (fun _ => d) (fun _ => d) z)) = splitValue := by
    funext z
    exact orderedClusterPrefixSplitAssignment_eq_sum_elim
      data c d v z
  calc
    MvPolynomial.eval₂Hom f v P =
        MvPolynomial.eval₂Hom f splitValue
          (MvPolynomial.rename e P) := hrename
    _ = MvPolynomial.eval₂Hom f
          (fun z => Sum.elim activeValue coefficientValue
            (splitClusterBlockSymbolEquiv
              (Fin (data.orderedCluster c).card)
              (data.OrderedClusterPrefixBlock c.val)
              (fun _ => d) (fun _ => d) z))
          (MvPolynomial.rename e P) := by rw [hsplit]
    _ = MvPolynomial.eval₂Hom
          (MvPolynomial.eval₂Hom f coefficientValue) activeValue
          (splitClusterCurryAlgEquiv R
            (Fin (data.orderedCluster c).card)
            (data.OrderedClusterPrefixBlock c.val)
            (fun _ => d) (fun _ => d)
            (MvPolynomial.rename e P)) :=
      eval₂Hom_splitClusterCurryAlgEquiv f
        (Fin (data.orderedCluster c).card)
        (data.OrderedClusterPrefixBlock c.val)
        (fun _ => d) (fun _ => d) activeValue coefficientValue
        (MvPolynomial.rename e P)
    _ = _ := rfl

@[simp]
theorem orderedClusterPrefixActiveAssignment_free
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (a : Fin (data.orderedCluster c).card) :
    orderedClusterPrefixActiveAssignment data c d v (Sum.inl a) =
      v (Sum.inl
        ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inl a))) := by
  rfl

@[simp]
theorem orderedClusterPrefixActiveAssignment_derivative
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (a : Fin (data.orderedCluster c).card) (r : Fin d) :
    orderedClusterPrefixActiveAssignment data c d v
        (Sum.inr (Sum.inl ⟨a, r⟩)) =
      v (Sum.inr (Sum.inl
        ⟨(data.orderedClusterPrefixSuccEquiv c).symm (Sum.inl a), r⟩)) := by
  apply congrArg v
  apply (data.orderedClusterPrefixOperationEquiv c d).injective
  simp [orderedClusterPrefixOperationEquiv, clusterOperationSymbolEquiv,
    splitClusterBlockSymbolEquiv]
  apply Sigma.ext
  · exact ((data.orderedClusterPrefixSuccEquiv c).apply_symm_apply
      (Sum.inl a)).symm
  · apply (Fin.heq_ext_iff (by simp)).2
    rfl

@[simp]
theorem orderedClusterPrefixActiveAssignment_time
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (a : Fin (data.orderedCluster c).card) :
    orderedClusterPrefixActiveAssignment data c d v
        (Sum.inr (Sum.inr a)) =
      v (Sum.inr (Sum.inr
        ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inl a)))) := by
  rfl

@[simp]
theorem orderedClusterPrefixCoefficientAssignment_free
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (b : data.OrderedClusterPrefixBlock c.val) :
    orderedClusterPrefixCoefficientAssignment data c d v (Sum.inl b) =
      v (Sum.inl
        ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b))) := by
  rfl

@[simp]
theorem orderedClusterPrefixCoefficientAssignment_derivative
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (b : data.OrderedClusterPrefixBlock c.val) (r : Fin d) :
    orderedClusterPrefixCoefficientAssignment data c d v
        (Sum.inr (Sum.inl ⟨b, r⟩)) =
      v (Sum.inr (Sum.inl
        ⟨(data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b), r⟩)) := by
  apply congrArg v
  apply (data.orderedClusterPrefixOperationEquiv c d).injective
  simp [orderedClusterPrefixOperationEquiv, clusterOperationSymbolEquiv,
    splitClusterBlockSymbolEquiv]
  apply Sigma.ext
  · exact ((data.orderedClusterPrefixSuccEquiv c).apply_symm_apply
      (Sum.inr b)).symm
  · apply (Fin.heq_ext_iff (by simp)).2
    rfl

@[simp]
theorem orderedClusterPrefixCoefficientAssignment_time
    {T : Type*} {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) (d : ℕ)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount d (c.val + 1)) → T)
    (b : data.OrderedClusterPrefixBlock c.val) :
    orderedClusterPrefixCoefficientAssignment data c d v
        (Sum.inr (Sum.inr b)) =
      v (Sum.inr (Sum.inr
        ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b)))) := by
  rfl

/-! ## Concrete active and coefficient values at one Hermite stage -/

/-- Concrete Hermite values on the active cluster at stage `c`. -/
def paperRankHermiteOrderedClusterActiveValue
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol (Fin (data.orderedCluster c).card)
      (fun _ => paperRankHermiteHigherCount S + 1) → ℝ :=
  orderedClusterPrefixActiveAssignment data c
    (paperRankHermiteHigherCount S + 1)
    (paperRankHermitePrefixValue data D representative offset S B F sw
      (c.val + 1))

/-- Concrete Hermite values on the surviving smaller prefix at stage `c`. -/
def paperRankHermiteOrderedClusterCoefficientValue
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol (data.OrderedClusterPrefixBlock c.val)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount S + 1) c.val) → ℝ :=
  orderedClusterPrefixCoefficientAssignment data c
    (paperRankHermiteHigherCount S + 1)
    (paperRankHermitePrefixValue data D representative offset S B F sw
      (c.val + 1))

@[simp]
theorem paperRankHermiteOrderedClusterActiveValue_free
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (a : Fin (data.orderedCluster c).card) :
    paperRankHermiteOrderedClusterActiveValue data D representative offset S
        B F sw c (Sum.inl a) =
      sw.1 (((data.orderedCluster c).equivFin).symm a).1 := by
  rfl

@[simp]
theorem paperRankHermiteOrderedClusterActiveValue_positiveDerivative
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (a : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermiteHigherCount S + 1)) :
    paperRankHermiteOrderedClusterActiveValue data D representative offset S
        B F sw c (Sum.inr (Sum.inl ⟨a, r⟩)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw
        (Sum.inr (((data.orderedCluster c).equivFin).symm a).1)
        (finCongr (paperRankHermiteHigherCount_add_one S) r).succ := by
  rw [paperRankHermiteOrderedClusterActiveValue,
    orderedClusterPrefixActiveAssignment_derivative,
    paperRankHermitePrefixValue_positiveDerivative]
  rfl

@[simp]
theorem paperRankHermiteOrderedClusterActiveValue_time
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (a : Fin (data.orderedCluster c).card) :
    paperRankHermiteOrderedClusterActiveValue data D representative offset S
        B F sw c (Sum.inr (Sum.inr a)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw
        (Sum.inr (((data.orderedCluster c).equivFin).symm a).1) 0 := by
  rfl

@[simp]
theorem paperRankHermiteOrderedClusterCoefficientValue_free
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    paperRankHermiteOrderedClusterCoefficientValue data D representative
        offset S B F sw c (Sum.inl b) = sw.1 b.1 := by
  rfl

@[simp]
theorem paperRankHermiteOrderedClusterCoefficientValue_positiveDerivative
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val)
    (r : Fin (paperRankHermiteHigherCount S + 1)) :
    paperRankHermiteOrderedClusterCoefficientValue data D representative
        offset S B F sw c (Sum.inr (Sum.inl ⟨b, r⟩)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr b.1)
        (finCongr (paperRankHermiteHigherCount_add_one S) r).succ := by
  rw [paperRankHermiteOrderedClusterCoefficientValue,
    orderedClusterPrefixCoefficientAssignment_derivative,
    paperRankHermitePrefixValue_positiveDerivative]
  rfl

@[simp]
theorem paperRankHermiteOrderedClusterCoefficientValue_time
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    paperRankHermiteOrderedClusterCoefficientValue data D representative
        offset S B F sw c (Sum.inr (Sum.inr b)) =
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ => F) sw (Sum.inr b.1) 0 := by
  rfl

/-- The stage form used by the quantitative trace: every prefix polynomial
evaluates by first specializing the smaller-prefix Hermite values and then
the concrete active-cluster Hermite values. -/
theorem eval_paperRankHermitePrefixValue_curry
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p)
    (c : Fin data.orderedClusterCount)
    (P : data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount S) (c.val + 1)) :
    MvPolynomial.eval
        (paperRankHermitePrefixValue data D representative offset S B F sw
          (c.val + 1)) P =
      MvPolynomial.eval₂Hom
        (MvPolynomial.eval
          (paperRankHermiteOrderedClusterCoefficientValue data D
            representative offset S B F sw c))
        (paperRankHermiteOrderedClusterActiveValue data D representative
          offset S B F sw c)
        (data.orderedClusterPrefixCurryAlgEquiv ℝ c
          (paperRankHermiteHigherCount S + 1) P) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (paperRankHermitePrefixValue data D representative offset S B F sw
        (c.val + 1)) P =
    MvPolynomial.eval₂Hom
      (MvPolynomial.eval₂Hom (RingHom.id ℝ)
        (paperRankHermiteOrderedClusterCoefficientValue data D
          representative offset S B F sw c))
      (paperRankHermiteOrderedClusterActiveValue data D representative
        offset S B F sw c)
      (data.orderedClusterPrefixCurryAlgEquiv ℝ c
        (paperRankHermiteHigherCount S + 1) P)
  exact eval₂Hom_orderedClusterPrefixCurryAlgEquiv
    (RingHom.id ℝ) data c (paperRankHermiteHigherCount S + 1)
    (paperRankHermitePrefixValue data D representative offset S B F sw
      (c.val + 1)) P

end RepresentativeClusterSubsequence
end AbelFormalization
