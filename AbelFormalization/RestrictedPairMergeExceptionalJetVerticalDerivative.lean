import AbelFormalization.RestrictedPairMergeExceptionalJetGraphLift
import AbelFormalization.FiniteImplicitRegularZeroGraphLift
import AbelFormalization.RegularZeroEquationScaling

/-!
# Vertical derivative of the finite exceptional pair-merge graph

The exceptional graph equations are coordinatewise in the appended graph
variables.  This file identifies their vertical Frechet derivative with a
positive diagonal continuous linear map and applies the maintained finite
implicit regular-zero graph-lift theorem.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- The branch-dependent pre-iterate argument is globally differentiable. -/
theorem differentiable_restrictedPairMergeExceptionalBaseArgument
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) (q : ι) :
    Differentiable ℝ
      (restrictedPairMergeExceptionalBaseArgument
        (p := p) (a := a) representative i j q) := by
  unfold restrictedPairMergeExceptionalBaseArgument
  split <;> fun_prop

/-- The simultaneous graph equation is differentiable wherever the original
pair-box coordinate is interior. -/
theorem differentiableAt_restrictedPairMergeExceptionalVectorGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    DifferentiableAt ℝ
      (restrictedPairMergeExceptionalVectorGraphEquation
        D representative offset K k i j S) (x, eta) := by
  apply differentiableAt_pi.mpr
  intro t
  let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
  let d := restrictedPairMergeExceptionalDepth representative K k i q
  let b := restrictedPairMergeExceptionalOldOffset D offset q
  have hv : DifferentiableAt ℝ
      (fun z : RestrictedSource (m + 1) (p + 1) a ×
          (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) ↦
        restrictedPairMergeExceptionalBaseArgument representative i j q z.1)
      (x, eta) :=
    (differentiable_restrictedPairMergeExceptionalBaseArgument
      (p := p) (a := a) representative i j q).differentiableAt.comp
        (x, eta) differentiableAt_fst
  have heta : DifferentiableAt ℝ
      (fun z : RestrictedSource (m + 1) (p + 1) a ×
          (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) ↦
        z.2 t) (x, eta) := by fun_prop
  have hbox : DifferentiableAt ℝ
      (fun z : RestrictedSource (m + 1) (p + 1) a ×
          (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) ↦
        z.1.1.2) (x, eta) := by fun_prop
  have hbAt : DifferentiableAt ℝ
      (b : RestrictedBoxSpace (p + 1) → ℝ) x.1.2 := by
    exact (((restrictedPairMergeBox D).analyticNearClosedBox_iff.mp b.property)
      x.1.2 ((restrictedPairMergeBox D).openBox_subset_closedBox hw)).differentiableAt
  have hb : DifferentiableAt ℝ
      (fun z : RestrictedSource (m + 1) (p + 1) a ×
          (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) ↦
        (b : RestrictedBoxSpace (p + 1) → ℝ) z.1.1.2) (x, eta) :=
    hbAt.comp (x, eta) hbox
  have hE : Differentiable ℝ (E^[d]) :=
    (contDiff_E_iterate d).differentiable (by simp)
  change DifferentiableAt ℝ
    (fun z ↦ E^[d]
        (restrictedPairMergeExceptionalBaseArgument representative i j q z.1 + z.2 t) -
      E^[d] (restrictedPairMergeExceptionalBaseArgument representative i j q z.1) -
      (b : RestrictedBoxSpace (p + 1) → ℝ) z.1.1.2) (x, eta)
  exact (hE.differentiableAt.comp (x, eta) (hv.add heta)).sub
    (hE.differentiableAt.comp (x, eta) hv) |>.sub hb

/-- The diagonal coefficient in the vertical graph derivative. -/
def restrictedPairMergeExceptionalVerticalCoefficient
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) :
    Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ :=
  fun t ↦ deriv
    (E^[restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)])
    (restrictedPairMergeExceptionalBaseArgument representative i j
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x + eta t)

theorem restrictedPairMergeExceptionalVerticalCoefficient_pos
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    0 < restrictedPairMergeExceptionalVerticalCoefficient
      representative K k i j S x eta t := by
  exact deriv_E_iterate_pos _ _

/-- The positive diagonal vertical map, packaged as a continuous linear
equivalence. -/
def restrictedPairMergeExceptionalVerticalEquiv
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) :
    (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) ≃L[ℝ]
      (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) :=
  coordinatewiseMulEquiv
    (restrictedPairMergeExceptionalVerticalCoefficient
      representative K k i j S x eta)
    (fun t ↦ (restrictedPairMergeExceptionalVerticalCoefficient_pos
      representative K k i j S x eta t).ne')

@[simp]
theorem restrictedPairMergeExceptionalVerticalEquiv_apply
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta v : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    restrictedPairMergeExceptionalVerticalEquiv
        representative K k i j S x eta v t =
      restrictedPairMergeExceptionalVerticalCoefficient
        representative K k i j S x eta t * v t := by
  simp [restrictedPairMergeExceptionalVerticalEquiv]

/-- The vertical Frechet derivative is the coordinatewise multiplication map
whose diagonal entries are the positive iterate derivatives. -/
theorem finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    finiteGraphLiftZBlock
        (fderiv ℝ
          (restrictedPairMergeExceptionalVectorGraphEquation
            D representative offset K k i j S) (x, eta)) =
      coordinatewiseMulCLM
        (restrictedPairMergeExceptionalVerticalCoefficient
          representative K k i j S x eta) := by
  let H := restrictedPairMergeExceptionalVectorGraphEquation
    (a := a) D representative offset K k i j S
  have hH : DifferentiableAt ℝ H (x, eta) :=
    differentiableAt_restrictedPairMergeExceptionalVectorGraphEquation
      D representative offset K k i j S x eta hw
  ext v t
  rw [coordinatewiseMulCLM_apply]
  let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
  let d := restrictedPairMergeExceptionalDepth representative K k i q
  let base : ℝ := restrictedPairMergeExceptionalBaseArgument representative i j q x
  let b : ℝ :=
    (restrictedPairMergeExceptionalOldOffset D offset q :
      RestrictedBoxSpace (p + 1) → ℝ) x.1.2
  have hpath : HasDerivAt
      (fun s : ℝ ↦ (x, eta + s • v))
      ((0, v) : RestrictedSource (m + 1) (p + 1) a ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)) 0 := by
    have hetaPath : HasDerivAt (fun s : ℝ ↦ eta + s • v) v 0 := by
      simpa using
        ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add eta
    exact (hasDerivAt_const (0 : ℝ) x).prodMk hetaPath
  have hH0 : HasFDerivAt H (fderiv ℝ H (x, eta)) (x, eta + (0 : ℝ) • v) := by
    simpa using hH.hasFDerivAt
  have hline := hH0.comp_hasDerivAt 0 hpath
  change HasDerivAt
    (fun s : ℝ ↦ H (x, eta + s • v))
    (fderiv ℝ H (x, eta) (0, v)) 0 at hline
  have hproj :=
    (ContinuousLinearMap.proj (R := ℝ) t).hasFDerivAt.comp_hasDerivAt 0 hline
  change HasDerivAt
    (fun s : ℝ ↦ H (x, eta + s • v) t)
    (finiteGraphLiftZBlock (fderiv ℝ H (x, eta)) v t) 0 at hproj
  have harg : HasDerivAt
      (fun s : ℝ ↦ base + eta t + s * v t) (v t) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v t)).const_add (base + eta t)
  have hmain :=
    ((hasDerivAt_E_iterate d (base + eta t + (0 : ℝ) * v t)).differentiableAt.hasDerivAt).comp
      0 harg
  have hcurve : HasDerivAt
      (fun s : ℝ ↦ E^[d] (base + eta t + s * v t) - E^[d] base - b)
      (deriv (E^[d]) (base + eta t) * v t) 0 := by
    simpa only [Function.comp_apply, zero_mul, add_zero] using
      (hmain.sub_const (E^[d] base)).sub_const b
  have hcurve' : HasDerivAt
      (fun s : ℝ ↦ H (x, eta + s • v) t)
      (deriv (E^[d]) (base + eta t) * v t) 0 := by
    convert hcurve using 1
    funext s
    simp [H, restrictedPairMergeExceptionalVectorGraphEquation,
      restrictedFixedIterateShiftGraphEquation, q, d, base, b, add_assoc]
  have heq := hproj.unique hcurve'
  simpa [H, restrictedPairMergeExceptionalVerticalCoefficient,
    q, d, base] using heq

/-- Equivalently, the vertical derivative is exactly the underlying map of
the positive diagonal continuous linear equivalence. -/
theorem finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation_eq_equiv
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    finiteGraphLiftZBlock
        (fderiv ℝ
          (restrictedPairMergeExceptionalVectorGraphEquation
            D representative offset K k i j S) (x, eta)) =
      (restrictedPairMergeExceptionalVerticalEquiv
        representative K k i j S x eta :
          (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) →L[ℝ]
            (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)) := by
  rw [finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation
    D representative offset K k i j S x eta hw]
  symm
  exact coordinatewiseMulEquiv_toContinuousLinearMap _ _

/-- The vertical derivative is surjective (indeed a positive diagonal
continuous linear equivalence). -/
theorem surjective_finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (eta : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    Function.Surjective
      (finiteGraphLiftZBlock
        (fderiv ℝ
          (restrictedPairMergeExceptionalVectorGraphEquation
            D representative offset K k i j S) (x, eta))) := by
  rw [finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation
    D representative offset K k i j S x eta hw]
  let c := restrictedPairMergeExceptionalVerticalCoefficient
    representative K k i j S x eta
  let e := coordinatewiseMulEquiv c fun t ↦
    (restrictedPairMergeExceptionalVerticalCoefficient_pos
      representative K k i j S x eta t).ne'
  rw [← coordinatewiseMulEquiv_toContinuousLinearMap c (fun t ↦
    (restrictedPairMergeExceptionalVerticalCoefficient_pos
      representative K k i j S x eta t).ne')]
  exact e.surjective

/-- The finite exceptional shift vector is differentiable on the simultaneous
quantitative tail. -/
theorem differentiableAt_restrictedPairMergeExceptionalVectorShift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    DifferentiableAt ℝ
      (restrictedPairMergeExceptionalVectorShift
        D representative offset K k i j S) x := by
  apply differentiableAt_pi.mpr
  intro t
  let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
  let d := restrictedPairMergeExceptionalDepth representative K k i q
  let b := restrictedPairMergeExceptionalOldOffset D offset q
  let phi : RestrictedSource (m + 1) (p + 1) a →
      ℝ × RestrictedBoxSpace (p + 1) := fun y ↦
    (restrictedPairMergeExceptionalBaseArgument representative i j q y, y.1.2)
  have hphi : DifferentiableAt ℝ phi x :=
    (differentiable_restrictedPairMergeExceptionalBaseArgument
      (p := p) (a := a) representative i j q).differentiableAt.prodMk (by
        fun_prop)
  have hshift : DifferentiableAt ℝ
      (restrictedFixedIterateShift d (restrictedPairMergeBox D) b) (phi x) :=
    differentiableAt_restrictedFixedIterateShift
      (restrictedPairMergeExceptionalDepth_pos representative (k := k) hK i q)
      (restrictedPairMergeBox D) b (hB t) (hbB t) (htail t) hw
  change DifferentiableAt ℝ
    (fun y ↦ restrictedFixedIterateShift d (restrictedPairMergeBox D) b (phi y)) x
  exact hshift.comp x hphi

/-- The simultaneous exceptional graph identity holds on a neighborhood of
every point satisfying all quantitative tail inequalities. -/
theorem eventuallyEq_restrictedPairMergeExceptionalVectorGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    (fun y ↦ restrictedPairMergeExceptionalVectorGraphEquation
        D representative offset K k i j S
        (y, restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S y)) =ᶠ[𝓝 x]
      (fun _ ↦ (0 :
        Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)) := by
  have hboxContinuous : ContinuousAt
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.2) x := by
    fun_prop
  have hbox : ∀ᶠ y in 𝓝 x,
      y.1.2 ∈ (restrictedPairMergeBox D).openBox :=
    hboxContinuous ((restrictedPairMergeBox D).isOpen_openBox.mem_nhds hw)
  have htails : ∀ᶠ y in 𝓝 x, ∀ t,
      B t + 2 < restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) y := by
    apply Filter.eventually_all.mpr
    intro t
    have hbaseContinuous : ContinuousAt
        (restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)) x :=
      (differentiable_restrictedPairMergeExceptionalBaseArgument
        (p := p) (a := a) representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)).continuous.continuousAt
    exact hbaseContinuous (isOpen_Ioi.mem_nhds (htail t))
  filter_upwards [hbox, htails] with y hy hytail
  exact restrictedPairMergeExceptionalVectorGraphEquation_on_shift
    D representative offset hK i j S B hB hbB y hy hytail

/-- Adjoining all exceptional fixed-iterate graph equations simultaneously
preserves regular-zero membership on the common quantitative tail. -/
theorem mem_regularZeroSet_restrictedPairMergeExceptionalFiniteGraphLift_iff
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    {Omega : Set (RestrictedSource (m + 1) (p + 1) a)}
    {Ftilde :
      RestrictedSource (m + 1) (p + 1) a ×
        (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) → Y}
    (hF : DifferentiableAt ℝ Ftilde
      (x, restrictedPairMergeExceptionalVectorShift
        D representative offset K k i j S x)) :
    x ∈ regularZeroSet Omega
        (finiteGraphSubstitution Ftilde
          (restrictedPairMergeExceptionalVectorShift
            D representative offset K k i j S)) ↔
      (x, restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S x) ∈
        regularZeroSet
          ((fun z : RestrictedSource (m + 1) (p + 1) a ×
              (Fin (restrictedPairMergeExceptionalOffsetSupport
                representative i j S).card → ℝ) ↦ z.1) ⁻¹' Omega)
          (finiteImplicitGraphLiftSystem Ftilde
            (restrictedPairMergeExceptionalVectorGraphEquation
              D representative offset K k i j S)) := by
  apply mem_regularZeroSet_finiteImplicitGraphLift_iff hF
    (differentiableAt_restrictedPairMergeExceptionalVectorGraphEquation
      D representative offset K k i j S x
        (restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S x) hw)
    (differentiableAt_restrictedPairMergeExceptionalVectorShift
      D representative offset hK i j S B hB hbB x hw htail)
    (eventuallyEq_restrictedPairMergeExceptionalVectorGraphEquation
      D representative offset hK i j S B hB hbB x hw htail)
  exact
    surjective_finiteGraphLiftZBlock_fderiv_restrictedPairMergeExceptionalVectorGraphEquation
      D representative offset K k i j S x
        (restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S x) hw

end AbelFormalization
