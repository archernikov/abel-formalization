import AbelFormalization.CharbonnelSourceStageWeakPreservation
import AbelFormalization.CharbonnelSardianIntegerAffineFrontierTrace
import AbelFormalization.CharbonnelSardianLiteralZeroLevelControls
import AbelFormalization.ProjectedZeroComplementCriterion

/-!
# Source-stage and rank bridges for the integer-affine Sardian step

This file joins the structural source hierarchy to the analytic trace
constructor of Wilkie 3.12.  The stage theorem is stated over an arbitrary
weak base family: if all members of one source stage already have Sardian
approximations, then the closed trace on one integer-affine hyperplane has a
Sardian approximation.  Weakness of that stage is obtained automatically
from weakness of the base family.

The second half carries out the numeric-rank bookkeeping for the maintained
description syntax.  Non-closure cases are replaced by strictly lower-rank
descriptions.  In the closure case, the exact and two strict predecessor
cuts also have lower-rank descriptions; the frontier-trace constructor
handles one genuine row, and further rows are imposed on an already closed,
empty-interior target.  This yields the full integer-affine rank input from
the geometric, smooth, and projection-constructor assumptions.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## A base-parametric source-stage approximation assertion -/

/-- Sardian approximability of every positive-arity member of one Wilkie
source stage over an arbitrary base family. -/
def WilkieSourceStageHasSardianApproximationsOver
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (S : EuclideanSetFamily) (i : ℕ) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {A : Set (RealEuclidean n)},
    A ∈ wilkieSourceStage S i n → HasSardianApproximationsForSet G A

theorem wilkieSourceStageHasSardianApproximationsOver_literalZero_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)} {i : ℕ} :
    WilkieSourceStageHasSardianApproximationsOver
        G (literalZeroSetFamily G) i ↔
      WilkieSourceStageHasSardianApproximations G i :=
  Iff.rfl

private theorem closure_inter_integerAffineSliceHyperplane_eq_exactClosure_of_zeroRow
    {n : ℕ} (B : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hzero : ∀ j : Fin n, coeff j = 0) :
    closure B ∩ integerAffineSliceHyperplane coeff constant =
      closure (B ∩ integerAffineSliceHyperplane coeff constant) := by
  by_cases hconstant : constant = 0
  · have hH : integerAffineSliceHyperplane coeff constant = Set.univ := by
      ext x
      simp [integerAffineSliceHyperplane, integerAffineSliceLinearForm,
        hzero, hconstant]
    simp [hH]
  · have hH : integerAffineSliceHyperplane coeff constant = ∅ := by
      ext x
      simp [integerAffineSliceHyperplane, integerAffineSliceLinearForm,
        hzero, hconstant]
    simp [hH]

/-- Wilkie 3.12--3.13 for one row at one source stage.  The three predecessor
cells remain in the same stage by WS1--WS2; their certificates are combined
with the two frontier-trace certificates.  A zero coefficient row is handled
by the exact cell, since its hyperplane is either all space or empty. -/
theorem WilkieSourceStageHasSardianApproximationsOver.integerAffineFrontierTrace
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {S : EuclideanSetFamily} {i n : ℕ}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hS : PositiveArityWeakSetStructure S)
    (hstage : WilkieSourceStageHasSardianApproximationsOver G S i)
    (hn : 0 < n) (B : Set (RealEuclidean n))
    (hB : B ∈ wilkieSourceStage S i n)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    HasSardianApproximationsForSet G
      (closure B ∩ integerAffineSliceHyperplane coeff constant) := by
  have hweak : PositiveArityWeakSetStructure (wilkieSourceStage S i) :=
    hS.wilkieSourceStagesAreWeak i
  obtain ⟨hexactMem, hpositiveMem, hnegativeMem⟩ :=
    wilkieSourceStage_integerAffineSlice_threeCuts
      hn hweak B hB coeff constant
  have hexact := hstage hn hexactMem
  have hpositive := hstage hn hpositiveMem
  have hnegative := hstage hn hnegativeMem
  intro order horder
  obtain ⟨exactCertificate⟩ := hexact order horder
  by_cases hnonzero : ∃ j : Fin n, coeff j ≠ 0
  · obtain ⟨positiveCertificate⟩ := hpositive order horder
    obtain ⟨negativeCertificate⟩ := hnegative order horder
    let positiveTrace := positiveIntegerAffineFrontierTraceCertificate
      hG hsmooth B coeff constant hnonzero positiveCertificate
    let negativeTrace := negativeIntegerAffineFrontierTraceCertificate
      hG hsmooth B coeff constant hnonzero negativeCertificate
    let first := exactCertificate.topologicalClosure.unionOfAnyHiddenArity
      positiveTrace
    let combined := first.unionOfAnyHiddenArity negativeTrace
    rw [closure_inter_integerAffineSliceHyperplane_three_piece]
    exact ⟨combined⟩
  · have hzero : ∀ j : Fin n, coeff j = 0 := by
      intro j
      by_contra hj
      exact hnonzero ⟨j, hj⟩
    rw [closure_inter_integerAffineSliceHyperplane_eq_exactClosure_of_zeroRow
      B coeff constant hzero]
    exact ⟨exactCertificate.topologicalClosure⟩

/-! ## The natural projected-zero base -/

/-- The projected-zero base is weak under the already formalized
smooth-geometric/UFF assumptions, so every source stage over it is weak. -/
theorem projectedZero_wilkieSourceStagesAreWeak
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    WilkieSourceStagesAreWeak (projectedZeroSetFamily G) :=
  (projectedZeroWeakStructureCertificate hG hsmooth hUFF).toPositiveArityOMinimalWeakStructure
    |>.toPositiveArityWeakSetStructure
    |>.wilkieSourceStagesAreWeak

/-- Literal generators embed in the projected-zero base. -/
theorem literalZeroSetFamily_le_projectedZeroSetFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)} :
    literalZeroSetFamily G ≤ projectedZeroSetFamily G := by
  intro n A hA
  obtain ⟨f, hf, rfl⟩ := hA
  refine ⟨0, f, hf, ?_⟩
  ext x
  simp

/-- The literal-zero base constructor plus the positive-projection
constructor already give Sardian approximations for every projected-zero
set, hence for stage zero of the natural weak base. -/
theorem wilkieProjectedZeroSourceStageHasSardianApproximations_zero
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G) :
    WilkieSourceStageHasSardianApproximationsOver
      G (projectedZeroSetFamily G) 0 := by
  intro n hn A hA order horder
  obtain ⟨q, f, hf, hA⟩ := hA
  let Z : Set (RealEuclidean (n + q)) := {v | f v = 0}
  have hAproj : A = realEuclideanExistentialProjection Z := by
    rw [hA]
    rfl
  by_cases hq : 0 < q
  · obtain ⟨old⟩ := hbase (by omega) f hf (order + q) (by omega)
    rw [hAproj]
    exact hprojection hn hq horder old
  · have hqzero : q = 0 := by omega
    subst q
    have hAZ : A = Z := hAproj.trans
      (realEuclideanExistentialProjection_zero Z)
    rw [hAZ]
    simpa only [Z, Nat.add_zero] using hbase hn f hf order horder

/-- Projected-zero specialization of the one-row stage trace theorem. -/
theorem projectedZeroSourceStage_integerAffineFrontierTrace
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {i n : ℕ}
    (hstage : WilkieSourceStageHasSardianApproximationsOver
      G (projectedZeroSetFamily G) i)
    (hn : 0 < n) (B : Set (RealEuclidean n))
    (hB : B ∈ wilkieSourceStage (projectedZeroSetFamily G) i n)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    HasSardianApproximationsForSet G
      (closure B ∩ integerAffineSliceHyperplane coeff constant) := by
  let hS : PositiveArityWeakSetStructure (projectedZeroSetFamily G) :=
    (projectedZeroWeakStructureCertificate hG hsmooth hUFF).toPositiveArityOMinimalWeakStructure
      |>.toPositiveArityWeakSetStructure
  exact hstage.integerAffineFrontierTrace hG hsmooth hS hn B hB
    coeff constant

/-! ## Repeated traces after the first genuine hyperplane -/

/-- The carrier of a displayed finite integer-affine system. -/
def integerAffineSliceSystemCarrier {n r : ℕ}
    (coeff : Fin r → Fin n → ℤ) (constant : Fin r → ℤ) :
    Set (RealEuclidean n) :=
  {x | ∀ i, integerAffineSliceLinearForm (coeff i) (constant i) x = 0}

@[simp]
theorem integerAffineSliceSystemCarrier_zero {n : ℕ}
    (coeff : Fin 0 → Fin n → ℤ) (constant : Fin 0 → ℤ) :
    integerAffineSliceSystemCarrier coeff constant = Set.univ := by
  ext x
  simp [integerAffineSliceSystemCarrier]

theorem integerAffineSliceSystemCarrier_succ {n r : ℕ}
    (coeff : Fin (r + 1) → Fin n → ℤ)
    (constant : Fin (r + 1) → ℤ) :
    integerAffineSliceSystemCarrier coeff constant =
      integerAffineSliceHyperplane (coeff 0) (constant 0) ∩
        integerAffineSliceSystemCarrier
          (fun i ↦ coeff i.succ) (fun i ↦ constant i.succ) := by
  ext x
  simp only [integerAffineSliceSystemCarrier,
    integerAffineSliceHyperplane, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact Fin.forall_fin_succ

/-- Once the target is closed with empty interior, every further affine-row
intersection is itself a frontier trace.  Thus the 3.12 constructor can be
iterated through an arbitrary finite system without any new predecessor
descriptions. -/
theorem exists_integerAffineSystemTraceCertificate_of_closed_emptyInterior
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n : ℕ} {A : Set (RealEuclidean n)}
    (old : CharbonnelSardianApproximationCertificate G order n A)
    (hclosed : IsClosed A) (hempty : interior A = ∅) :
    ∀ {r : ℕ} (coeff : Fin r → Fin n → ℤ)
      (constant : Fin r → ℤ),
      Nonempty (CharbonnelSardianApproximationCertificate G order n
        (A ∩ integerAffineSliceSystemCarrier coeff constant)) := by
  intro r
  induction r generalizing A with
  | zero =>
      intro coeff constant
      simpa only [integerAffineSliceSystemCarrier_zero, Set.inter_univ]
        using (show Nonempty
          (CharbonnelSardianApproximationCertificate G order n A) from
            ⟨old⟩)
  | succ r ih =>
      intro coeff constant
      let H := integerAffineSliceHyperplane (coeff 0) (constant 0)
      have htrace : closure A ∩ H = frontier (closure A) ∩ H := by
        rw [hclosed.closure_eq, hclosed.frontier_eq, hempty]
        simp
      let first := wilkieAffineSliceFrontierTraceCertificate
        hG hsmooth old (coeff 0) (constant 0) htrace
      let A₁ : Set (RealEuclidean n) := closure A ∩ H
      have hA₁closed : IsClosed A₁ :=
        isClosed_closure.inter
          (isClosed_integerAffineSliceHyperplane (coeff 0) (constant 0))
      have hA₁subset : A₁ ⊆ A := by
        intro x hx
        simpa only [A₁, hclosed.closure_eq] using hx.1
      have hA₁empty : interior A₁ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxA : x ∈ interior A := interior_mono hA₁subset hx
        rw [hempty] at hxA
        exact hxA
      obtain ⟨rest⟩ := ih (A := A₁) first hA₁closed hA₁empty
        (fun i ↦ coeff i.succ) (fun i ↦ constant i.succ)
      refine ⟨?_⟩
      simpa only [A₁, hclosed.closure_eq,
        integerAffineSliceSystemCarrier_succ, Set.inter_assoc] using rest

private theorem interior_integerAffineSliceHyperplane_eq_empty
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0) :
    interior (integerAffineSliceHyperplane coeff constant) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨radius, hradius, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) x hx
  obtain ⟨_y, hyBall, hyNegative⟩ :=
    (exists_integerAffineSlice_nearby_strictSigns
      coeff constant hnonzero x (interior_subset hx) hradius).1
  have hyH := interior_subset (hball hyBall)
  exact (ne_of_lt hyNegative) hyH

/-! ## Numeric-rank predecessor cuts -/

/-- The three predecessor certificates in the hard closure branch can be
obtained from the numeric strong-induction hypothesis with three ranks to
spare.  Strict sign cells are projected-zero sets, hence have rank-one
literal-zero descriptions; the general intersection construction then has
rank at most `3 + B.rank`. -/
theorem exists_integerAffineFrontierTraceCertificate_of_rankIH
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {r order n : ℕ}
    (ih : ∀ {m : ℕ}
      (lower : CharbonnelDescription (literalZeroSetFamily G) m),
        lower.rank < r → lower.HasSardianApproximations G)
    (B : CharbonnelDescription (literalZeroSetFamily G) n)
    (hbudget : 3 + B.rank < r)
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    (horder : 0 < order) :
    Nonempty (CharbonnelSardianApproximationCertificate G order n
      (closure B.carrier ∩
        integerAffineSliceHyperplane coeff constant)) := by
  let H := integerAffineSliceHyperplane coeff constant
  let P := integerAffineSlicePositiveSide coeff constant
  let N := integerAffineSliceNegativeSide coeff constant
  let exactDescription :
      CharbonnelDescription (literalZeroSetFamily G) n :=
    .integerAffineInter B H
      (isIntegerAffineSet_integerAffineSliceHyperplane coeff constant)
  have hexactRank : exactDescription.rank < r := by
    simp only [exactDescription, CharbonnelDescription.rank_integerAffineInter]
    omega
  obtain ⟨exactCertificate⟩ := ih exactDescription hexactRank order horder
  have hPprojected : IsProjectedZeroSet G P :=
    (polynomialSignConstructible_integerAffineSlicePositiveSide
      coeff constant).isProjectedZeroSet hG
  have hNprojected : IsProjectedZeroSet G N :=
    (polynomialSignConstructible_integerAffineSliceNegativeSide
      coeff constant).isProjectedZeroSet hG
  obtain ⟨positiveDescription, hpositiveCarrier, hpositiveRank⟩ :=
    hPprojected.exists_rank_one_literalZero_description B.positiveArity
  obtain ⟨negativeDescription, hnegativeCarrier, hnegativeRank⟩ :=
    hNprojected.exists_rank_one_literalZero_description B.positiveArity
  obtain ⟨positiveCut, hpositiveCutCarrier, hpositiveCutRank⟩ :=
    literalZeroSetFamily_exists_inter_description
      hG hsmooth B positiveDescription
  obtain ⟨negativeCut, hnegativeCutCarrier, hnegativeCutRank⟩ :=
    literalZeroSetFamily_exists_inter_description
      hG hsmooth B negativeDescription
  have hpositiveCutLt : positiveCut.rank < r := by omega
  have hnegativeCutLt : negativeCut.rank < r := by omega
  obtain ⟨positiveCertificate₀⟩ :=
    ih positiveCut hpositiveCutLt order horder
  obtain ⟨negativeCertificate₀⟩ :=
    ih negativeCut hnegativeCutLt order horder
  have exactCertificate' :
      CharbonnelSardianApproximationCertificate G order n
        (B.carrier ∩ H) := by
    simpa only [exactDescription,
      CharbonnelDescription.carrier_integerAffineInter] using
        exactCertificate
  have positiveCertificate :
      CharbonnelSardianApproximationCertificate G order n
        (B.carrier ∩ P) := by
    simpa only [hpositiveCutCarrier, hpositiveCarrier] using
      positiveCertificate₀
  have negativeCertificate :
      CharbonnelSardianApproximationCertificate G order n
        (B.carrier ∩ N) := by
    simpa only [hnegativeCutCarrier, hnegativeCarrier] using
      negativeCertificate₀
  let positiveTrace := positiveIntegerAffineFrontierTraceCertificate
    hG hsmooth B.carrier coeff constant hnonzero positiveCertificate
  let negativeTrace := negativeIntegerAffineFrontierTraceCertificate
    hG hsmooth B.carrier coeff constant hnonzero negativeCertificate
  let first := exactCertificate'.topologicalClosure.unionOfAnyHiddenArity
    positiveTrace
  let combined := first.unionOfAnyHiddenArity negativeTrace
  rw [closure_inter_integerAffineSliceHyperplane_three_piece]
  exact ⟨combined⟩

private theorem integerAffineSliceSystemCarrier_eq_univ_or_empty_of_zeroRows
    {n r : ℕ} (coeff : Fin r → Fin n → ℤ)
    (constant : Fin r → ℤ)
    (hzero : ∀ i j, coeff i j = 0) :
    integerAffineSliceSystemCarrier coeff constant = Set.univ ∨
      integerAffineSliceSystemCarrier coeff constant = ∅ := by
  by_cases hconstant : ∀ i, constant i = 0
  · left
    ext x
    simp [integerAffineSliceSystemCarrier, integerAffineSliceLinearForm,
      hzero, hconstant]
  · right
    push Not at hconstant
    obtain ⟨i, hi⟩ := hconstant
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hrow := hx i
    simp only [integerAffineSliceLinearForm] at hrow
    have hsum : (∑ j : Fin n, (coeff i j : ℝ) * x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      simp [hzero i j]
    rw [hsum, zero_add] at hrow
    exact hi (by exact_mod_cast hrow)

@[simp]
private theorem realEuclideanSetProduct_univ_zero {n : ℕ}
    (A : Set (RealEuclidean n)) :
    realEuclideanSetProduct A (Set.univ : Set (RealEuclidean 0)) = A := by
  ext x
  have htake : realEuclideanTakeLeft x = x := by
    calc
      realEuclideanTakeLeft x =
          realEuclideanAppend (realEuclideanTakeLeft x)
            (realEuclideanTakeRight x) :=
        (realEuclideanAppend_zero _ _).symm
      _ = x := realEuclideanAppend_takeLeft_takeRight x
  simp [realEuclideanSetProduct, htake]

/-! ## The full maintained integer-affine rank input -/

/-- Wilkie's integer-affine rank branch follows from the already formalized
3.12 frontier trace, smooth geometric closure, and the positive-projection
constructor.  No additional stage/rank premise is required.

For a closure node, one genuine row first creates a closed trace contained in
a proper hyperplane.  It therefore has empty interior, allowing all remaining
rows of an arbitrary finite integer-affine system to be added by repeated
frontier traces.  If every row has zero linear part, the system is either all
space or empty and the exact lower-rank cut suffices. -/
theorem charbonnelSardianIntegerAffineRankInput_of_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G) :
    CharbonnelSardianIntegerAffineRankInput G := by
  intro r ih n inner L hL hrank
  cases inner with
  | base hn A hA =>
      have hLbase : L ∈ literalZeroSetFamily G n :=
        hL.mem_literalZeroSetFamily hG
      have hinter : A ∩ L ∈ literalZeroSetFamily G n :=
        literalZeroSetFamily_inter_mem hG hA hLbase
      let replacement :
          CharbonnelDescription (literalZeroSetFamily G) n :=
        .base hn (A ∩ L) hinter
      have hreplacementRank : replacement.rank < r := by
        simp only [replacement, CharbonnelDescription.rank_base,
          CharbonnelDescription.rank_integerAffineInter] at hrank ⊢
        omega
      simpa only [CharbonnelDescription.HasSardianApproximations,
        CharbonnelDescription.carrier_integerAffineInter,
        CharbonnelDescription.carrier_base, replacement] using
          ih replacement hreplacementRank
  | union left right =>
      let leftCut : CharbonnelDescription (literalZeroSetFamily G) n :=
        .integerAffineInter left L hL
      let rightCut : CharbonnelDescription (literalZeroSetFamily G) n :=
        .integerAffineInter right L hL
      have hleftRank : leftCut.rank < r := by
        simp only [leftCut, CharbonnelDescription.rank_integerAffineInter,
          CharbonnelDescription.rank_union] at hrank ⊢
        omega
      have hrightRank : rightCut.rank < r := by
        simp only [rightCut, CharbonnelDescription.rank_integerAffineInter,
          CharbonnelDescription.rank_union] at hrank ⊢
        omega
      have hunion := (ih leftCut hleftRank).union (ih rightCut hrightRank)
      simpa only [CharbonnelDescription.HasSardianApproximations,
        CharbonnelDescription.carrier_integerAffineInter,
        CharbonnelDescription.carrier_union, leftCut, rightCut,
        Set.union_inter_distrib_right] using hunion
  | integerAffineInter base K hK =>
      have hKL : IsIntegerAffineSet (K ∩ L) := hK.inter hL
      let replacement :
          CharbonnelDescription (literalZeroSetFamily G) n :=
        .integerAffineInter base (K ∩ L) hKL
      have hreplacementRank : replacement.rank < r := by
        simp only [replacement, CharbonnelDescription.rank_integerAffineInter]
          at hrank ⊢
        omega
      simpa only [CharbonnelDescription.HasSardianApproximations,
        CharbonnelDescription.carrier_integerAffineInter, replacement,
        Set.inter_assoc] using ih replacement hreplacementRank
  | @projection visible hidden hvisible lifted =>
      let cylinder : Set (RealEuclidean (n + hidden)) :=
        realEuclideanSetProduct L
          (Set.univ : Set (RealEuclidean hidden))
      have hcylinder : IsIntegerAffineSet cylinder :=
        hL.prod_univ_right hidden
      let replacement :
          CharbonnelDescription (literalZeroSetFamily G)
            (n + hidden) :=
        .integerAffineInter lifted cylinder hcylinder
      have hreplacementRank : replacement.rank < r := by
        simp only [replacement, CharbonnelDescription.rank_integerAffineInter,
          CharbonnelDescription.rank_projection] at hrank ⊢
        omega
      have hreplacement := ih replacement hreplacementRank
      intro order horder
      have htarget := realEuclideanExistentialProjection_inter_product_univ
        lifted.carrier L
      by_cases hhidden : 0 < hidden
      · obtain ⟨old⟩ := hreplacement (order + hidden) (by omega)
        have hnew := hprojection hvisible hhidden horder old
        simpa only [CharbonnelDescription.carrier_integerAffineInter,
          CharbonnelDescription.carrier_projection, replacement, cylinder,
          htarget] using hnew
      · have hzero : hidden = 0 := by omega
        subst hidden
        obtain ⟨old⟩ := hreplacement order horder
        refine ⟨?_⟩
        simpa only [Nat.add_zero,
          CharbonnelDescription.carrier_integerAffineInter,
          CharbonnelDescription.carrier_projection, replacement, cylinder,
          realEuclideanSetProduct_univ_zero,
          realEuclideanExistentialProjection_zero, htarget] using old
  | topologicalClosure base =>
      obtain ⟨rows, coeff, constant, hLpresentation⟩ :=
        hL.exists_sliceHyperplane_presentation
      have hLsystem :
          L = integerAffineSliceSystemCarrier coeff constant := by
        rw [hLpresentation]
        ext x
        simp only [Set.mem_iInter, integerAffineSliceHyperplane,
          integerAffineSliceSystemCarrier, Set.mem_ofPred_eq]
      let exactDescription :
          CharbonnelDescription (literalZeroSetFamily G) n :=
        .integerAffineInter base L hL
      have hexactRank : exactDescription.rank < r := by
        simp only [exactDescription,
          CharbonnelDescription.rank_integerAffineInter,
          CharbonnelDescription.rank_topologicalClosure] at hrank ⊢
        omega
      have hexact := ih exactDescription hexactRank
      intro order horder
      change Nonempty (CharbonnelSardianApproximationCertificate
        G order n (closure base.carrier ∩ L))
      by_cases hnonzero : ∃ i : Fin rows, ∃ j : Fin n, coeff i j ≠ 0
      · obtain ⟨i, hi⟩ := hnonzero
        have hbudget : 3 + base.rank < r := by
          simp only [CharbonnelDescription.rank_integerAffineInter,
            CharbonnelDescription.rank_topologicalClosure] at hrank
          omega
        obtain ⟨first⟩ :=
          exists_integerAffineFrontierTraceCertificate_of_rankIH
            hG hsmooth ih base hbudget (coeff i) (constant i) hi horder
        let H := integerAffineSliceHyperplane (coeff i) (constant i)
        let A₁ : Set (RealEuclidean n) := closure base.carrier ∩ H
        have hA₁closed : IsClosed A₁ :=
          isClosed_closure.inter
            (isClosed_integerAffineSliceHyperplane (coeff i) (constant i))
        have hA₁subset : A₁ ⊆ H := Set.inter_subset_right
        have hHint : interior H = ∅ :=
          interior_integerAffineSliceHyperplane_eq_empty
            (coeff i) (constant i) hi
        have hA₁empty : interior A₁ = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxH : x ∈ interior H := interior_mono hA₁subset hx
          rw [hHint] at hxH
          exact hxH
        obtain ⟨answer⟩ :=
          exists_integerAffineSystemTraceCertificate_of_closed_emptyInterior
            hG hsmooth first hA₁closed hA₁empty coeff constant
        have htarget :
            A₁ ∩ integerAffineSliceSystemCarrier coeff constant =
              closure base.carrier ∩ L := by
          rw [hLsystem]
          ext x
          simp only [A₁, H, Set.mem_inter_iff,
            integerAffineSliceSystemCarrier, Set.mem_ofPred_eq,
            integerAffineSliceHyperplane]
          constructor
          · rintro ⟨⟨hxClosure, _hxRow⟩, hxSystem⟩
            exact ⟨hxClosure, hxSystem⟩
          · rintro ⟨hxClosure, hxSystem⟩
            exact ⟨⟨hxClosure, hxSystem i⟩, hxSystem⟩
        rw [← htarget]
        exact ⟨answer⟩
      · have hzero : ∀ i j, coeff i j = 0 := by
          intro i j
          by_contra hij
          exact hnonzero ⟨i, j, hij⟩
        obtain hsystem | hsystem :=
          integerAffineSliceSystemCarrier_eq_univ_or_empty_of_zeroRows
            coeff constant hzero
        · have htarget : closure base.carrier ∩ L =
              closure (base.carrier ∩ L) := by
            rw [hLsystem, hsystem]
            simp
          obtain ⟨exactCertificate⟩ := hexact order horder
          rw [htarget]
          exact ⟨exactCertificate.topologicalClosure⟩
        · have htarget : closure base.carrier ∩ L =
              closure (base.carrier ∩ L) := by
            rw [hLsystem, hsystem]
            simp
          obtain ⟨exactCertificate⟩ := hexact order horder
          rw [htarget]
          exact ⟨exactCertificate.topologicalClosure⟩

/-- With the affine branch now proved, the global rank step needs only the
literal-zero base constructor and positive-projection constructor. -/
theorem charbonnelSardianApproximationRankStep_of_base_and_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G) :
    CharbonnelSardianApproximationRankStep G :=
  charbonnelSardianApproximationRankStep_of_constructorInputs
    hbase hprojection
      (charbonnelSardianIntegerAffineRankInput_of_projection
        hG hsmooth hprojection)

/-- Smooth geometric families supply the literal-zero base constructor, so
the positive-projection constructor is the only remaining input to the full
numeric Sardian rank step. -/
theorem charbonnelSardianApproximationRankStep_of_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G) :
    CharbonnelSardianApproximationRankStep G :=
  charbonnelSardianApproximationRankStep_of_base_and_projection
    hG hsmooth
      (charbonnelSardianLiteralZeroBaseInput_of_smoothGeometric hG hsmooth)
      hprojection

/-- All maintained descriptions consequently have Sardian approximations
once the base and positive-projection constructors are available. -/
theorem CharbonnelDescription.hasSardianApproximations_of_base_and_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    description.HasSardianApproximations G :=
  description.hasSardianApproximations_of_constructorInputs
    hbase hprojection
      (charbonnelSardianIntegerAffineRankInput_of_projection
        hG hsmooth hprojection)

/-- Every maintained description has Sardian approximations from the
positive-projection constructor alone, under the standing smooth geometric
family hypotheses. -/
theorem CharbonnelDescription.hasSardianApproximations_of_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    description.HasSardianApproximations G :=
  description.hasSardianApproximations_of_base_and_projection
    hG hsmooth
      (charbonnelSardianLiteralZeroBaseInput_of_smoothGeometric hG hsmooth)
      hprojection

/-- The rank bridge closes the source-stage induction globally: every member
of every literal-zero source stage has Sardian approximations once the
positive-projection constructor is available. -/
theorem wilkieSourceStageHasSardianApproximations_of_projection
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (i : ℕ) :
    WilkieSourceStageHasSardianApproximations G i := by
  intro n hn A hA
  have hclosure : A ∈ charbonnelClosure (literalZeroSetFamily G) n :=
    wilkieSourceStage_le_charbonnelClosure
      (literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
        hG hsmooth)
      i hn hA
  obtain ⟨description, hdescription⟩ := hclosure
  rw [← hdescription]
  exact (description.hasSardianApproximations_iff_set).mp
    (description.hasSardianApproximations_of_projection
      hG hsmooth hprojection)

end AbelFormalization
