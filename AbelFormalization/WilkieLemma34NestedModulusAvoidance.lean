import AbelFormalization.MaxwellLocalFiberCardinality
import AbelFormalization.CharbonnelSardianCertificatePadding

/-!
# Wilkie Lemma 3.4: nested modulus avoidance

An empty-interior member of the Charbonnel closure can be avoided by all
parameter tails bounded by one nested modulus.  The proof is the arity
induction from Wilkie's Lemma 3.4.

The unary case uses WS5 to make the member finite.  At a successor arity,
Maxwell's local fiber-cardinality argument gives a uniform component bound
and shows that the locus with one more fiber point has empty interior.  The
induction hypothesis avoids that locus, so every remaining scalar fiber is
finite.  The final modulus bound is then chosen below the least positive
point of that finite fiber.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite subsets of the line are absent near zero on the right -/

/-- A finite subset of `ℝ` misses some punctured interval immediately to
the right of zero. -/
theorem exists_positive_interval_avoiding_finite_set
    {s : Set ℝ} (hs : s.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < y → y < δ → y ∉ s := by
  let t : Set ℝ := s \ {0}
  have htFinite : t.Finite := hs.subset Set.diff_subset
  have hzero : (0 : ℝ) ∈ tᶜ := by
    simp [t]
  have hnhds : tᶜ ∈ nhds (0 : ℝ) :=
    htFinite.isClosed.isOpen_compl.mem_nhds hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro y hy hless hys
  have hyball : y ∈ Metric.ball (0 : ℝ) δ := by
    change dist y 0 < δ
    simpa [Real.dist_eq, abs_of_pos hy] using hless
  have hycompl : y ∈ tᶜ := hball hyball
  apply hycompl
  exact ⟨hys, by simpa using ne_of_gt hy⟩

/-- A fixed positive bound witnessing right-hand avoidance of a finite set. -/
def finitePositiveAvoidanceBound (s : Set ℝ) (hs : s.Finite) : ℝ :=
  Classical.choose (exists_positive_interval_avoiding_finite_set hs)

theorem finitePositiveAvoidanceBound_pos
    (s : Set ℝ) (hs : s.Finite) :
    0 < finitePositiveAvoidanceBound s hs :=
  (Classical.choose_spec
    (exists_positive_interval_avoiding_finite_set hs)).1

theorem not_mem_of_pos_lt_finitePositiveAvoidanceBound
    (s : Set ℝ) (hs : s.Finite) {y : ℝ}
    (hy : 0 < y) (hless : y < finitePositiveAvoidanceBound s hs) :
    y ∉ s :=
  (Classical.choose_spec
    (exists_positive_interval_avoiding_finite_set hs)).2 y hy hless

/-! ## The unary base case -/

/-- WS5 makes an empty-interior unary family member finite.  This is the
vector-valued form used in the arity induction. -/
theorem PositiveArityOMinimalWeakSetStructure.finite_unary_member
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {A : Set (RealEuclidean 1)} (hA : A ∈ C 1)
    (hinterior : interior A = ∅) : A.Finite := by
  have hcoordinateInterior :
      interior (realEuclideanOneCoordinateImage A) = ∅ := by
    rw [realEuclideanOneCoordinateImage_eq_equivImage]
    change interior (realEuclideanOneEquivReal.toHomeomorph '' A) = ∅
    rw [← realEuclideanOneEquivReal.toHomeomorph.image_interior]
    simp [hinterior]
  have hcoordinateFinite :
      (realEuclideanOneCoordinateImage A).Finite :=
    (hC.coordinateImage_unaryPieceDecomposable hA)
      |>.finite_of_interior_eq_empty hcoordinateInterior
  have himageFinite : (realEuclideanOneEquivReal '' A).Finite := by
    rwa [← realEuclideanOneCoordinateImage_eq_equivImage]
  exact himageFinite.of_finite_image
    realEuclideanOneEquivReal.injective.injOn

/-! ## Wilkie's arity induction -/

/-- Wilkie's Lemma 3.4.  Every positive-arity, empty-interior member of the
Charbonnel closure admits a nested modulus all of whose bounded parameter
tails lie outside the member. -/
theorem wilkieLemma34_exists_nested_modulus_avoiding
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {k : ℕ} (hk : 0 < k)
    {A : Set (RealEuclidean k)}
    (hA : A ∈ charbonnelClosure S k)
    (hinterior : interior A = ∅) :
    ∃ modulus : CharbonnelModulus k,
      ∀ ε : RealEuclidean (k + 1), modulus.IsBounded ε →
        CharbonnelModulus.parameterTail ε ∉ A := by
  classical
  have inductionStatement : ∀ p : ℕ,
      ∀ (B : Set (RealEuclidean (p + 1))),
        B ∈ charbonnelClosure S (p + 1) →
        interior B = ∅ →
        ∃ modulus : CharbonnelModulus (p + 1),
          ∀ ε : RealEuclidean ((p + 1) + 1), modulus.IsBounded ε →
            CharbonnelModulus.parameterTail ε ∉ B := by
    intro p
    induction p with
    | zero =>
        intro B hB hBInterior
        have hBFinite : B.Finite :=
          hC.finite_unary_member hB hBInterior
        let coordinateSet : Set ℝ := realEuclideanOneCoordinateImage B
        have hcoordinateFinite : coordinateSet.Finite := by
          exact hBFinite.image fun v : RealEuclidean 1 ↦ v 0
        let δ : ℝ :=
          finitePositiveAvoidanceBound coordinateSet hcoordinateFinite
        let initial : CharbonnelModulus 0 :=
          .base 1 zero_lt_one
        let modulus : CharbonnelModulus 1 :=
          .step initial (fun _ ↦ δ)
            (fun _ _ ↦
              finitePositiveAvoidanceBound_pos
                coordinateSet hcoordinateFinite)
        refine ⟨modulus, ?_⟩
        intro ε hε htail
        change initial.IsBounded (Fin.init ε) ∧
            0 < ε (Fin.last 1) ∧ ε (Fin.last 1) < δ at hε
        have hcoordinateMem : ε (Fin.last 1) ∈ coordinateSet := by
          refine ⟨CharbonnelModulus.parameterTail ε, htail, ?_⟩
          simp [CharbonnelModulus.parameterTail]
        exact
          (not_mem_of_pos_lt_finitePositiveAvoidanceBound
            coordinateSet hcoordinateFinite hε.2.1 hε.2.2)
            hcoordinateMem
    | succ p ih =>
        intro B hB hBInterior
        let base : Set (RealEuclidean (p + 1)) := Set.univ
        obtain ⟨N, _hcomponentBound, hlargeInterior⟩ :=
          exists_component_bound_and_interior_atLeast_succ_eq_empty_of_category
            hC (p := p + 1) (by omega)
              (B := base) (R := B) hB hBInterior
        let large : Set (RealEuclidean (p + 1)) :=
          maxwellScalarFiberCardinalityAtLeast base B (N + 1)
        have hbase : base ∈ charbonnelClosure S (p + 1) :=
          hC.ws2_polynomialSign (by omega)
            (polynomialSignConstructible_univ (p + 1))
        have hlarge : large ∈ charbonnelClosure S (p + 1) :=
          maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
            hC.toPositiveArityWeakSetStructure (by omega) hbase hB
        obtain ⟨initial, hinitialAvoids⟩ :=
          ih large hlarge hlargeInterior
        have hfiberFinite
            (pfx : RealEuclidean ((p + 1) + 1))
            (hpfx : initial.IsBounded pfx) :
            (maxwellScalarFiber B
              (CharbonnelModulus.parameterTail pfx)).Finite := by
          have hnotLarge :
              CharbonnelModulus.parameterTail pfx ∉ large :=
            hinitialAvoids pfx hpfx
          have hnotSucc :
              ¬ (N + 1 : ℕ∞) ≤
                (maxwellScalarFiber B
                  (CharbonnelModulus.parameterTail pfx)).encard := by
            intro hsucc
            apply hnotLarge
            exact
              (mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
                base B (CharbonnelModulus.parameterTail pfx)).mpr
                ⟨Set.mem_univ _, hsucc⟩
          have hupper :
              (maxwellScalarFiber B
                (CharbonnelModulus.parameterTail pfx)).encard ≤
                (N : ℕ∞) := by
            by_contra hnotUpper
            have hlt : (N : ℕ∞) <
                (maxwellScalarFiber B
                  (CharbonnelModulus.parameterTail pfx)).encard :=
              lt_of_not_ge hnotUpper
            have hsucc : (N + 1 : ℕ∞) ≤
                (maxwellScalarFiber B
                  (CharbonnelModulus.parameterTail pfx)).encard := by
              rw [ENat.natCast_add_one_le_iff]
              exact hlt
            exact hnotSucc hsucc
          exact Set.finite_of_encard_le_coe hupper
        let lastBound (pfx : RealEuclidean ((p + 1) + 1)) : ℝ :=
          if hpfx : initial.IsBounded pfx then
            finitePositiveAvoidanceBound
              (maxwellScalarFiber B
                (CharbonnelModulus.parameterTail pfx))
              (hfiberFinite pfx hpfx)
          else
            1
        have hlastBoundPos : ∀ pfx : RealEuclidean ((p + 1) + 1),
            (∀ i, 0 < pfx i) → 0 < lastBound pfx := by
          intro pfx _hpositive
          by_cases hpfx : initial.IsBounded pfx
          · simp only [lastBound, dif_pos hpfx]
            exact finitePositiveAvoidanceBound_pos _
              (hfiberFinite pfx hpfx)
          · simp [lastBound, hpfx]
        let modulus : CharbonnelModulus ((p + 1) + 1) :=
          .step initial lastBound hlastBoundPos
        refine ⟨modulus, ?_⟩
        intro ε hε htail
        change initial.IsBounded (Fin.init ε) ∧
            0 < ε (Fin.last ((p + 1) + 1)) ∧
            ε (Fin.last ((p + 1) + 1)) < lastBound (Fin.init ε) at hε
        have hlastLess :
            ε (Fin.last ((p + 1) + 1)) <
              finitePositiveAvoidanceBound
                (maxwellScalarFiber B
                  (CharbonnelModulus.parameterTail (Fin.init ε)))
                (hfiberFinite (Fin.init ε) hε.1) := by
          simpa only [lastBound, dif_pos hε.1] using hε.2.2
        have hlastNotMem :
            ε (Fin.last ((p + 1) + 1)) ∉
              maxwellScalarFiber B
                (CharbonnelModulus.parameterTail (Fin.init ε)) :=
          not_mem_of_pos_lt_finitePositiveAvoidanceBound _
            (hfiberFinite (Fin.init ε) hε.1) hε.2.1 hlastLess
        apply hlastNotMem
        rw [mem_maxwellScalarFiber_iff]
        rw [charbonnelParameterTail_eq_appendLastParameter_init_last] at htail
        exact htail
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact inductionStatement p A hA hinterior

end AbelFormalization
