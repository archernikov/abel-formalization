import AbelFormalization.CharbonnelSardianProjectionRegularModulus
import AbelFormalization.CharbonnelSardianProjectionLocalAssembly
import AbelFormalization.CharbonnelComplementPipeline

/-!
# One-coordinate Sardian projection

This file joins the critical-value avoidance modulus to the complete local
geometric assembly.  The resulting theorem isolates the sole analytic input
left in Wilkie's one-coordinate projection step: empty interior of the finite
exact-depth critical-parameter set.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Reassociation of a visible block, a hidden prefix, and the final erased
coordinate.  For a final one-dimensional block the two ambient arities are
definitionally equal, but the `Fin.addCases` presentations still need this
extensional proof. -/
theorem realEuclideanAppend_assoc_last
    {n q : ℕ} (x : RealEuclidean n) (y : RealEuclidean q)
    (z : RealEuclidean 1) :
    realEuclideanAppend x (realEuclideanAppend y z) =
      realEuclideanAppend (realEuclideanAppend x y) z := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [realEuclideanAppend_castAdd]
    rw [show Fin.castAdd (q + 1) i =
      Fin.castAdd 1 (Fin.castAdd q i) by apply Fin.ext; rfl]
    simp only [realEuclideanAppend_castAdd]
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun l ↦ ?_) j
    · simp only [realEuclideanAppend_natAdd,
        realEuclideanAppend_castAdd]
      rw [show Fin.natAdd n (Fin.castAdd 1 i) =
        Fin.castAdd 1 (Fin.natAdd n i) by apply Fin.ext; rfl]
      simp only [realEuclideanAppend_castAdd,
        realEuclideanAppend_natAdd]
    · simp only [realEuclideanAppend_natAdd]
      rw [show Fin.natAdd n (Fin.natAdd q l) =
        Fin.natAdd (n + q) l by apply Fin.ext; simp [Fin.natAdd]]
      simp only [realEuclideanAppend_natAdd]

/-- Projecting a final coordinate and then a block of `q` coordinates is the
same set as projecting the combined block of `q + 1` coordinates. -/
theorem realEuclideanExistentialProjection_succ
    {n q : ℕ} (A : Set (RealEuclidean (n + (q + 1)))) :
    realEuclideanExistentialProjection (n := n) (m := q + 1) A =
      realEuclideanExistentialProjection (n := n) (m := q)
        (realEuclideanExistentialProjection
          (n := n + q) (m := 1) A) := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨yz, hyz⟩
    let y : RealEuclidean q := realEuclideanTakeLeft yz
    let z : RealEuclidean 1 := realEuclideanTakeRight yz
    refine ⟨y, z, ?_⟩
    have hsplit : realEuclideanAppend y z = yz :=
      realEuclideanAppend_takeLeft_takeRight yz
    rw [← realEuclideanAppend_assoc_last x y z, hsplit]
    exact hyz
  · rintro ⟨y, z, hxyz⟩
    refine ⟨realEuclideanAppend y z, ?_⟩
    rw [realEuclideanAppend_assoc_last x y z]
    exact hxyz

/-- The one-coordinate form of the positive Sardian projection constructor. -/
def CharbonnelSardianOneCoordinateProjectionInput
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n order : ℕ} (hn : 0 < n) (horder : 0 < order)
    {A : Set (RealEuclidean (n + 1))},
      CharbonnelSardianApproximationCertificate
          G (order + 1) (n + 1) A →
        Nonempty (CharbonnelSardianApproximationCertificate G order n
          (realEuclideanExistentialProjection A))

/-- Iterating the one-coordinate constructor supplies Wilkie's constructor
for an arbitrary positive block of erased coordinates. -/
theorem CharbonnelSardianOneCoordinateProjectionInput.toProjectionConstructor
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hone : CharbonnelSardianOneCoordinateProjectionInput G) :
    CharbonnelSardianProjectionConstructorInput G := by
  intro n q order hn _hq A horder old
  have inductionStatement : ∀ q : ℕ,
      ∀ {n order : ℕ}, 0 < n → 0 < order →
      ∀ {A : Set (RealEuclidean (n + q))},
        CharbonnelSardianApproximationCertificate
            G (order + q) (n + q) A →
          Nonempty (CharbonnelSardianApproximationCertificate G order n
            (realEuclideanExistentialProjection A)) := by
    intro q
    induction q with
    | zero =>
        intro n order _hn _horder A certificate
        simpa only [Nat.add_zero,
          realEuclideanExistentialProjection_zero] using
          (show Nonempty (CharbonnelSardianApproximationCertificate
            G order n A) from ⟨certificate⟩)
    | succ q ih =>
        intro n order hn horder A certificate
        obtain ⟨first⟩ := hone (n := n + q) (order := order + q)
          (by omega) (by omega) certificate
        obtain ⟨rest⟩ := ih hn horder first
        rw [realEuclideanExistentialProjection_succ A]
        exact ⟨rest⟩
  exact inductionStatement q hn horder old

/-- Empty interior of the exact-depth critical parameters supplies the full
one-coordinate Sardian projection certificate. -/
theorem exists_sardianProjectionCertificate_of_criticalValuesInteriorEqEmpty
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    {order n : ℕ} (horder : 0 < order) (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      (abelGeometricFamily f) (order + 1) (n + 1) A)
    (hcritical :
      interior
        (old.family.exactDepthProjectionCriticalParameterSet
          hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
          hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1) = ∅) :
    Nonempty (CharbonnelSardianApproximationCertificate
      (abelGeometricFamily f) order n
      (realEuclideanExistentialProjection A)) := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hf.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hweak : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  obtain ⟨regularModulus, hrefines, hregular⟩ :=
    exists_sardianProjectionRegularModulus
      hG hsmooth hderiv hweak old hcritical
  exact ⟨sardianProjectionCertificate_of_regularModulus
    hf hUFF h21 h22 horder hn old regularModulus hrefines hregular⟩

/-- If the exact critical-parameter set is small for every one-coordinate
old certificate, the full arbitrary-block projection premise follows. -/
theorem IsAbel.charbonnelSardianProjectionConstructorInput_of_criticalValues
    {f : ℝ → ℝ} (hf : IsAbel f)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily f))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily f))))
    (hcritical : ∀ {order n : ℕ} (_horder : 0 < order) (_hn : 0 < n)
      {A : Set (RealEuclidean (n + 1))}
      (old : CharbonnelSardianApproximationCertificate
        (abelGeometricFamily f) (order + 1) (n + 1) A),
        interior
          (old.family.exactDepthProjectionCriticalParameterSet
            hf.geometric_smooth_derivativeClosed_abelGeometricFamily.1
            hf.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1) =
          ∅) :
    CharbonnelSardianProjectionConstructorInput
      (abelGeometricFamily f) := by
  apply CharbonnelSardianOneCoordinateProjectionInput.toProjectionConstructor
  intro n order hn horder A old
  exact exists_sardianProjectionCertificate_of_criticalValuesInteriorEqEmpty
    hf hUFF h21 h22 horder hn old (hcritical horder hn old)

end AbelFormalization
