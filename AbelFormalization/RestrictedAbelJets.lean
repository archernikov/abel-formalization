import AbelFormalization.RestrictedExpressionDifferentiation
import AbelFormalization.Stirling

/-!
# Shifted Abel jets in the restricted expression base

The special generators in the manuscript are all derivatives
`A⁽ʳ⁾(s_i + b(w))`, for a fixed collection of analytic offsets `b`.  Their
directional derivative is the next jet multiplied by the directional
derivative of the argument.  Since every derivative order is present, this
closes the last hypothesis of the restricted-expression differentiation
theorem.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- One shifted argument `s_i + b(w)` on a restricted source. -/
def restrictedAbelArgument {m p a : ℕ} (i : Fin m)
    (b : RestrictedBoxSpace p → ℝ) : RestrictedSource m p a → ℝ :=
  restrictedSCoordinate (p := p) (a := a) i +
    restrictedBoxCoefficientPullback (m := m) (a := a) b

@[simp]
theorem restrictedAbelArgument_apply {m p a : ℕ} (i : Fin m)
    (b : RestrictedBoxSpace p → ℝ) (x : RestrictedSource m p a) :
    restrictedAbelArgument i b x = x.1.1 i + b x.1.2 :=
  rfl

/-- The `r`th Abel derivative evaluated at one shifted source argument. -/
def restrictedAbelJet (A : ℝ → ℝ) {m p a : ℕ} (i : Fin m)
    (b : RestrictedBoxSpace p → ℝ) (r : ℕ) :
    RestrictedSource m p a → ℝ :=
  iteratedDeriv r A ∘ restrictedAbelArgument i b

@[simp]
theorem restrictedAbelJet_apply (A : ℝ → ℝ) {m p a : ℕ} (i : Fin m)
    (b : RestrictedBoxSpace p → ℝ) (r : ℕ)
    (x : RestrictedSource m p a) :
    restrictedAbelJet A i b r x =
      iteratedDeriv r A (x.1.1 i + b x.1.2) :=
  rfl

/-- All shifted Abel jets for the supplied family of offsets.  The offset
index type may be infinite; any element of the generated algebra still uses
only finitely many generators. -/
def restrictedAbelJetGenerators (A : ℝ → ℝ) {m p a : ℕ}
    {D : RestrictedBox p} (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    Set (RestrictedSource m p a → ℝ) :=
  Set.range fun kr : ι × ℕ ↦
    restrictedAbelJet A (representative kr.1)
      (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2

/-- The domain on which all named Abel arguments are positive and the box
coordinate lies in the closed box.  The manuscript's open domain is a subset
of this cylinder, with positivity ensured by its choice of `R`. -/
def restrictedAbelJetDomain {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    Set (RestrictedSource m p a) :=
  restrictedClosedBoxCylinder D ∩
    {x | ∀ k, 0 < restrictedAbelArgument (representative k)
      (offset k : RestrictedBoxSpace p → ℝ) x}

theorem restrictedAbelJetDomain_subset_closedBoxCylinder
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedAbelJetDomain (a := a) D representative offset ⊆
      restrictedClosedBoxCylinder D :=
  Set.inter_subset_left

theorem restrictedAbelArgument_pos
    {m p a : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin m}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    {x : RestrictedSource m p a}
    (hx : x ∈ restrictedAbelJetDomain D representative offset) (k : ι) :
    0 < restrictedAbelArgument (representative k)
      (offset k : RestrictedBoxSpace p → ℝ) x :=
  hx.2 k

/-- Directional derivative of one shifted Abel argument. -/
def restrictedAbelArgumentDirectionalDerivative
    {m p a : ℕ} {D : RestrictedBox p}
    (v : RestrictedSource m p a) (i : Fin m)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    RestrictedSource m p a → ℝ :=
  (fun _ ↦ v.1.1 i) +
    restrictedBoxCoefficientPullback (m := m) (a := a)
      (D.directionalDerivative v.1.2 b : RestrictedBoxSpace p → ℝ)

@[simp]
theorem restrictedAbelArgumentDirectionalDerivative_apply
    {m p a : ℕ} {D : RestrictedBox p}
    (v : RestrictedSource m p a) (i : Fin m)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (x : RestrictedSource m p a) :
    restrictedAbelArgumentDirectionalDerivative v i b x =
      v.1.1 i + fderiv ℝ (b : RestrictedBoxSpace p → ℝ) x.1.2 v.1.2 :=
  rfl

theorem restrictedAbelArgumentDirectionalDerivative_mem_base
    {m p a : ℕ} {D : RestrictedBox p}
    (A : ℝ → ℝ) (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (v : RestrictedSource m p a) (i : Fin m)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedAbelArgumentDirectionalDerivative v i b ∈
      restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a) A representative offset) := by
  apply (restrictedExpressionBase D
    (restrictedAbelJetGenerators (a := a) A representative offset)).add_mem
  · exact (restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)).algebraMap_mem
        (v.1.1 i)
  · exact restrictedBoxCoefficientPullback_mem_base D _
      (D.directionalDerivative v.1.2 b)

/-- The shifted-argument chain rule, restricted to the common positive Abel
domain. -/
theorem hasDirectionalDerivOn_restrictedAbelArgument
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (v : RestrictedSource m p a) (k : ι) :
    HasDirectionalDerivOn
      (restrictedAbelJetDomain (a := a) D representative offset) v
      (restrictedAbelArgument (representative k)
        (offset k : RestrictedBoxSpace p → ℝ))
      (restrictedAbelArgumentDirectionalDerivative v
        (representative k) (offset k)) := by
  exact
    ((hasDirectionalDerivOn_restrictedSCoordinate D v (representative k)).add
      (hasDirectionalDerivOn_restrictedBoxCoefficientPullback D v (offset k))).mono
        (restrictedAbelJetDomain_subset_closedBoxCylinder
          (a := a) D representative offset)

/-- The derivative of the `r`th shifted Abel jet is the `(r+1)`st jet times
the derivative of its shifted argument. -/
theorem IsAbel.hasDirectionalDerivOn_restrictedAbelJet
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (v : RestrictedSource m p a) (k : ι) (r : ℕ) :
    HasDirectionalDerivOn
      (restrictedAbelJetDomain (a := a) D representative offset) v
      (restrictedAbelJet A (representative k)
        (offset k : RestrictedBoxSpace p → ℝ) r)
      (restrictedAbelJet A (representative k)
          (offset k : RestrictedBoxSpace p → ℝ) (r + 1) *
        restrictedAbelArgumentDirectionalDerivative v
          (representative k) (offset k)) := by
  intro x hx
  have harg := hasDirectionalDerivOn_restrictedAbelArgument
    D representative offset v k x hx
  have houter := hA.hasDerivAt_iteratedDeriv r
    (restrictedAbelArgument_pos hx k)
  have hcomp := houter.comp_hasFDerivAt x harg.1.hasFDerivAt
  constructor
  · exact hcomp.differentiableAt
  · have happ := congrArg
      (fun L : RestrictedSource m p a →L[ℝ] ℝ ↦ L v) hcomp.fderiv
    simpa [restrictedAbelJet, harg.2, smul_eq_mul] using happ

/-- The complete family of Abel-jet special generators is directionally
closed inside its restricted expression base. -/
theorem IsAbel.restrictedAbelJetGenerators_directionallyClosed
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (v : RestrictedSource m p a) :
    SpecialGeneratorsDirectionallyClosed D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (restrictedAbelJetDomain (a := a) D representative offset) v := by
  intro f hf
  obtain ⟨⟨k, r⟩, rfl⟩ := hf
  let darg := restrictedAbelArgumentDirectionalDerivative v
    (representative k) (offset k)
  let df := restrictedAbelJet A (representative k)
    (offset k : RestrictedBoxSpace p → ℝ) (r + 1) * darg
  refine ⟨df, ?_, ?_⟩
  · apply (restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)).mul_mem
    · apply specialGenerator_mem_base D
      exact ⟨(k, r + 1), rfl⟩
    · exact restrictedAbelArgumentDirectionalDerivative_mem_base
        A representative offset v (representative k) (offset k)
  · exact hA.hasDirectionalDerivOn_restrictedAbelJet
      representative offset v k r

/-- Consequently every level of every finite exponential list over the
shifted Abel-jet base is closed under differentiation in the chosen source
direction. -/
theorem IsAbel.restrictedAbelTower_directionallyClosedOn_level
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (v : RestrictedSource m p a) (j : ℕ) :
    DirectionallyClosedOn (T.level j)
      (restrictedAbelJetDomain (a := a) D representative offset) v :=
  T.directionallyClosedOn_level
    (restrictedAbelJetDomain (a := a) D representative offset) v
    (restrictedAbelJetDomain_subset_closedBoxCylinder
      (a := a) D representative offset)
    (hA.restrictedAbelJetGenerators_directionallyClosed
      representative offset v) j

end AbelFormalization
