import AbelFormalization.ReciprocalConstraintGraph
import AbelFormalization.SmoothFamilySelectedOutputClosure
import AbelFormalization.SmoothFamilyRankStratumFiberReduction

/-!
# Targetwise finiteness of global maximal-rank fiber pieces

Assume a smooth family map has derivative rank at most `k` everywhere.  Its
rank-`k` part in one fixed fiber is covered by the finitely many patches on
which a selected `k × k` Jacobian minor is nonzero.

On one such patch the corresponding selected-output derivative is
surjective.  Adding one reciprocal variable for the nonzero minor produces a
closed, globally regular constraint zero locus.  The arbitrary-codimension
Lagrange theorem makes its connected components finite, and the reciprocal
graph homeomorphism transfers this to the selected-output patch.  The full
fiber is clopen inside that patch because the global rank bound makes the
unselected outputs locally constant along selected-output fibers.

All statements are for a specified target, or quantify `∀ t` outside the
finiteness assertion.  No common cardinal bound is produced.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Selected-minor patches -/

/-- The selected-output fiber patch on which one chosen square Jacobian minor
does not vanish. -/
def selectedMinorFiberPatch {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    Set (RealEuclidean a) :=
  reciprocalConstraintPatch
    (fun i x ↦ g x (rows i) - t (rows i))
    (standardJacobianMinor g rows cols)

@[simp]
theorem mem_selectedMinorFiberPatch {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (x : RealEuclidean a) :
    x ∈ selectedMinorFiberPatch g t rows cols ↔
      (∀ i, g x (rows i) = t (rows i)) ∧
        standardJacobianMinor g rows cols x ≠ 0 := by
  simp only [selectedMinorFiberPatch, mem_reciprocalConstraintPatch]
  constructor
  · rintro ⟨hselected, hminor⟩
    exact ⟨fun i ↦ sub_eq_zero.mp (hselected i), hminor⟩
  · rintro ⟨hselected, hminor⟩
    exact ⟨fun i ↦ sub_eq_zero.mpr (hselected i), hminor⟩

/-- The part of the exact-rank fiber piece detected by one selected minor. -/
def maximalRankFiberMinorPatch {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    Set (standardJacobianRankFiberPiece g t k) :=
  {x | standardJacobianMinor g rows cols (x : RealEuclidean a) ≠ 0}

/-- Inside a selected-minor patch, retain the points of the full fiber. -/
def fullFiberInSelectedMinorPatch {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    Set (selectedMinorFiberPatch g t rows cols) :=
  {x | g (x : RealEuclidean a) = t}

/-! ## Finiteness of one reciprocal patch -/

/-- Every selected-output nonzero-minor patch has finitely many connected
components under the four smooth-family hypotheses. -/
theorem finite_connectedComponents_selectedMinorFiberPatch
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    Finite (ConnectedComponents (selectedMinorFiberPatch g t rows cols)) := by
  let H : Fin k → RealEuclideanFunction a :=
    fun i x ↦ g x (rows i) - t (rows i)
  let q : RealEuclideanFunction a := standardJacobianMinor g rows cols
  let system : Fin (k + 1) → RealEuclideanFunction (a + 1) :=
    reciprocalGraphConstraintSystem H q
  have hHmem : ∀ i, H i ∈ G a := by
    intro i
    exact hG.sub_mem (hg (rows i)) (hG.const_mem (t (rows i)))
  have hqmem : q ∈ G a := by
    exact hG.standardJacobianMinor_mem hderiv g hg rows cols
  have hsystemmem : ∀ r, system r ∈ G (a + 1) := by
    exact hG.reciprocalGraphConstraintSystem_mem H q hHmem hqmem
  have hgInf : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun x ↦ g x i) (hg i)
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth a (H i) (hHmem i)
  have hqinf : ContDiff ℝ ∞ q :=
    hsmooth a q hqmem
  have hsystemSurj : ∀ z : RealEuclidean (a + 1),
      z ∈ constraintZeroLocus system →
        (constraintFDeriv system z).range = ⊤ := by
    intro z hz
    let x : RealEuclidean a := lagrangePrimalProjection a 1 z
    let u : ℝ := z (Fin.natAdd a (0 : Fin 1))
    have hgraph := hz (Fin.last k)
    have hgraph' : u * q x - 1 = 0 := by
      simpa only [system, reciprocalGraphConstraintSystem_last, x, u] using hgraph
    have hqne : q x ≠ 0 := by
      intro hqzero
      rw [hqzero, mul_zero] at hgraph'
      norm_num at hgraph'
    have hselectedSurj : Function.Surjective
        (fderiv ℝ (selectedOutputMap g rows) x) :=
      fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
        ((hgInf.differentiable (by simp)).differentiableAt)
        rows cols (by simpa only [q] using hqne)
    have hHdiff : ∀ i, DifferentiableAt ℝ (H i) x := by
      intro i
      exact (hHinf i).differentiable (by simp) |>.differentiableAt
    have hconstraintEq :
        constraintFDeriv H x =
          fderiv ℝ (selectedOutputMap g rows) x := by
      have htupleDeriv :
          fderiv ℝ (constraintMap H) x = constraintFDeriv H x := by
        change fderiv ℝ (fun y i ↦ H i y) x =
          ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (H i) x)
        exact fderiv_pi hHdiff
      calc
        constraintFDeriv H x = fderiv ℝ (constraintMap H) x :=
          htupleDeriv.symm
        _ = fderiv ℝ
            (fun y ↦ selectedOutputMap g rows y -
              (fun i ↦ t (rows i))) x := by rfl
        _ = fderiv ℝ (selectedOutputMap g rows) x := by
          rw [fderiv_sub_const]
    have hHsurj : (constraintFDeriv H x).range = ⊤ := by
      rw [hconstraintEq]
      exact LinearMap.range_eq_top.mpr hselectedSurj
    have hzsplit : realEuclideanAppendScalar x u = z := by
      change (realEuclideanAppendScalarContinuousLinearEquiv a)
          ((realEuclideanAppendScalarContinuousLinearEquiv a).symm z) = z
      exact (realEuclideanAppendScalarContinuousLinearEquiv a).apply_symm_apply z
    rw [← hzsplit]
    apply reciprocalGraphConstraintSystem_constraintFDeriv_range_eq_top
      H q x u hHdiff
    · exact hqinf.differentiable (by simp) |>.differentiableAt
    · exact hHsurj
    · exact hqne
    · intro r
      exact (hsmooth (a + 1) (system r) (hsystemmem r)).differentiable
        (by simp) |>.differentiableAt
  have hgraphFinite :
      Finite (ConnectedComponents (constraintZeroLocus system)) :=
    finite_connectedComponents_constraintZeroLocus_generalCodimension
      hG hsmooth hderiv hzero system hsystemmem hsystemSurj
  have hqcont : Continuous q := hqinf.continuous
  let e : reciprocalConstraintPatch H q ≃ₜ constraintZeroLocus system := by
    simpa only [system] using reciprocalConstraintPatchHomeomorph H q hqcont
  change Finite (ConnectedComponents (reciprocalConstraintPatch H q))
  let _ : Finite (ConnectedComponents (constraintZeroLocus system)) :=
    hgraphFinite
  exact Finite.of_surjective e.symm.continuous.connectedComponentsMap
    (e.symm.continuous.connectedComponentsMap_surjective e.symm.surjective)

/-! ## The full fiber is clopen in a selected patch -/

/-- Under the global rank bound, the full fiber is clopen inside every
selected nonzero-minor patch. -/
theorem isClopen_fullFiberInSelectedMinorPatch_of_rank_le
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hrank : ∀ x : RealEuclidean a,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k) :
    IsClopen (fullFiberInSelectedMinorPatch g t rows cols) := by
  constructor
  · exact isClosed_eq
      (hg.continuous.comp continuous_subtype_val) continuous_const
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    have hminor : standardJacobianMinor g rows cols
        (y : RealEuclidean a) ≠ 0 :=
      y.property.2
    obtain ⟨U, hUopen, hyU, hlocal⟩ :=
      exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
        hg (y : RealEuclidean a) rows cols hminor
          (Filter.Eventually.of_forall hrank)
    have hUnhds : Subtype.val ⁻¹' U ∈ nhds y :=
      (hUopen.preimage continuous_subtype_val).mem_nhds hyU
    refine mem_of_superset hUnhds ?_
    intro z hzU
    have hselected : selectedOutputMap g rows (z : RealEuclidean a) =
        selectedOutputMap g rows (y : RealEuclidean a) := by
      funext i
      exact (sub_eq_zero.mp (z.property.1 i)).trans
        (sub_eq_zero.mp (y.property.1 i)).symm
    exact (hlocal z hzU y hyU hselected).trans hy

/-! ## Projection to the exact-rank fiber patch -/

/-- A chosen full-fiber minor patch has finitely many connected components.
The proof projects its clopen realization inside the selected-output patch. -/
theorem finite_connectedComponents_maximalRankFiberMinorPatch
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hrank : ∀ x : RealEuclidean a,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k) :
    Finite (ConnectedComponents
      (maximalRankFiberMinorPatch g t rows cols)) := by
  have hgInf : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun x ↦ g x i) (hg i)
  have hselectedFinite :
      Finite (ConnectedComponents (selectedMinorFiberPatch g t rows cols)) :=
    finite_connectedComponents_selectedMinorFiberPatch
      hG hsmooth hderiv hzero g hg t rows cols
  let _ : Finite
      (ConnectedComponents (selectedMinorFiberPatch g t rows cols)) :=
    hselectedFinite
  have hclopen := isClopen_fullFiberInSelectedMinorPatch_of_rank_le
    g (hgInf.of_le (by norm_num)) t rows cols hrank
  have hfullFinite : Finite (ConnectedComponents
      (fullFiberInSelectedMinorPatch g t rows cols)) :=
    finite_connectedComponents_clopen_subtype hclopen
  have hrankEq_of_minor : ∀ x : RealEuclidean a,
      standardJacobianMinor g rows cols x ≠ 0 →
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) = k := by
    intro x hminor
    have hgdiff : DifferentiableAt ℝ g x :=
      (hgInf.differentiable (by simp)).differentiableAt
    have hlowerMatrix : k ≤ (standardRectangularJacobian g x).rank :=
      (matrix_le_rank_iff_exists_square_minor_ne_zero
        (standardRectangularJacobian g x)).mpr
          ⟨rows, cols, hminor⟩
    have hlower : k ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) := by
      rw [← standardRectangularJacobian_rank_eq_finrank_range_fderiv hgdiff]
      exact hlowerMatrix
    exact le_antisymm (hrank x) hlower
  let drop : fullFiberInSelectedMinorPatch g t rows cols →
      maximalRankFiberMinorPatch g t rows cols := fun y ↦
    ⟨⟨⟨(y : RealEuclidean a), Set.mem_singleton_iff.mpr y.property⟩,
      hrankEq_of_minor y y.1.property.2⟩, y.1.property.2⟩
  have hdropContinuous : Continuous drop := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous
      (Subtype.val : selectedMinorFiberPatch g t rows cols →
        RealEuclidean a)).comp
      (continuous_subtype_val : Continuous
        (Subtype.val : fullFiberInSelectedMinorPatch g t rows cols →
          selectedMinorFiberPatch g t rows cols))
  have hdropSurjective : Function.Surjective drop := by
    intro z
    have hgt : g (z : RealEuclidean a) = t :=
      Set.mem_singleton_iff.mp z.1.1.property
    let y : selectedMinorFiberPatch g t rows cols :=
      ⟨(z : RealEuclidean a), (mem_selectedMinorFiberPatch
        g t rows cols (z : RealEuclidean a)).mpr
          ⟨fun i ↦ congrFun hgt (rows i), z.property⟩⟩
    let yfull : fullFiberInSelectedMinorPatch g t rows cols :=
      ⟨y, hgt⟩
    refine ⟨yfull, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let _ : Finite (ConnectedComponents
      (fullFiberInSelectedMinorPatch g t rows cols)) := hfullFinite
  exact Finite.of_surjective hdropContinuous.connectedComponentsMap
    (hdropContinuous.connectedComponentsMap_surjective hdropSurjective)

/-! ## Finite cover of the global maximal-rank fiber piece -/

/-- If the derivative rank is globally at most `k`, then the exact-rank-`k`
piece of one fixed fiber has finitely many connected components. -/
theorem finite_connectedComponents_globalMaximalRankFiberPiece
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (hrank : ∀ x : RealEuclidean a,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k)
    (t : RealEuclidean b) :
    Finite (ConnectedComponents (standardJacobianRankFiberPiece g t k)) := by
  let I := (Fin k ↪ Fin b) × (Fin k ↪ Fin a)
  let patches : I → Set (standardJacobianRankFiberPiece g t k) :=
    fun rc ↦ maximalRankFiberMinorPatch g t rc.1 rc.2
  have hgInf : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun x ↦ g x i) (hg i)
  have hcover : ⋃ rc, patches rc = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxrank : Module.finrank ℝ
        (LinearMap.range
          (fderiv ℝ g (x : RealEuclidean a)).toLinearMap) = k :=
      x.property
    have hminor :=
      (finrank_range_fderiv_eq_iff_standardJacobianMinors
        ((hgInf.differentiable (by simp)).differentiableAt)).mp hxrank |>.1
    obtain ⟨rows, cols, hne⟩ := hminor
    rw [Set.mem_iUnion]
    exact ⟨(rows, cols), hne⟩
  apply finite_connectedComponents_of_finite_iUnion_cover patches hcover
  intro rc
  exact finite_connectedComponents_maximalRankFiberMinorPatch
    hG hsmooth hderiv hzero g hg t rc.1 rc.2 hrank

/-- Targetwise form of maximal-rank-piece finiteness.  The finite instance is
chosen separately for every target. -/
theorem forall_target_finite_connectedComponents_globalMaximalRankFiberPiece
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (hrank : ∀ x : RealEuclidean a,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap) ≤ k) :
    ∀ t : RealEuclidean b,
      Finite (ConnectedComponents (standardJacobianRankFiberPiece g t k)) := by
  intro t
  exact finite_connectedComponents_globalMaximalRankFiberPiece
    hG hsmooth hderiv hzero g hg hrank t

end AbelFormalization
