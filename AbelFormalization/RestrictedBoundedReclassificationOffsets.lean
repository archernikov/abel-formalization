import AbelFormalization.RestrictedBoundedReclassificationDomain

/-!
# Scratch: offsets after bounded-representative reclassification

For a chosen old representative coordinate, the offset labels split into
those supported on that coordinate and those supported on one of the
remaining coordinates.  The latter remain Abel-jet labels after the source
reclassification.  The former become analytic functions of the enlarged box.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Offset labels whose representative survives removal of the chosen
coordinate. -/
abbrev RestrictedRetainedOffsetIndex {m : ℕ}
    (representative : ι → Fin (m + 1)) (i : Fin (m + 1)) :=
  {k : ι // representative k ≠ i}

/-- Offset labels whose representative becomes the new final bounded
coordinate. -/
abbrev RestrictedPivotOffsetIndex {m : ℕ}
    (representative : ι → Fin (m + 1)) (i : Fin (m + 1)) :=
  {k : ι // representative k = i}

/-- Delete the chosen representative coordinate from a retained label. -/
def restrictedReclassifiedRepresentative {m : ℕ}
    (representative : ι → Fin (m + 1)) (i : Fin (m + 1)) :
    RestrictedRetainedOffsetIndex representative i → Fin m :=
  fun k ↦ (finSuccAboveEquiv i).symm
    ⟨representative k.1, k.2⟩

@[simp]
theorem succAbove_restrictedReclassifiedRepresentative {m : ℕ}
    (representative : ι → Fin (m + 1)) (i : Fin (m + 1))
    (k : RestrictedRetainedOffsetIndex representative i) :
    i.succAbove (restrictedReclassifiedRepresentative representative i k) =
      representative k.1 := by
  have h := congrArg Subtype.val
    ((finSuccAboveEquiv i).apply_symm_apply
      (⟨representative k.1, k.2⟩ :
        {j : Fin (m + 1) // j ≠ i}))
  simpa only [finSuccAboveEquiv_apply,
    restrictedReclassifiedRepresentative] using h

/-- Forget the final coordinate of an enlarged restricted box. -/
def restrictedBoxInitCLM (p : ℕ) :
    RestrictedBoxSpace (p + 1) →L[ℝ] RestrictedBoxSpace p :=
  ContinuousLinearMap.pi fun j ↦
    ContinuousLinearMap.proj (R := ℝ) j.castSucc

@[simp]
theorem restrictedBoxInitCLM_apply (p : ℕ)
    (w : RestrictedBoxSpace (p + 1)) (j : Fin p) :
    restrictedBoxInitCLM p w j = w j.castSucc :=
  rfl

/-- Pull an analytic coefficient on `D` back along the projection which
forgets the newly appended interval. -/
def RestrictedBox.pullbackSnoc {p : ℕ} (D : RestrictedBox p)
    (l u : ℝ) (hlu : l < u)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    RestrictedBox.analyticNearClosedBoxSubalgebra (D.snoc l u hlu) :=
  ⟨fun w ↦ (f : RestrictedBoxSpace p → ℝ)
      (restrictedBoxInitCLM p w), by
    change (D.snoc l u hlu).AnalyticNearClosedBox
      (fun w ↦ (f : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p w))
    rw [(D.snoc l u hlu).analyticNearClosedBox_iff]
    intro w hw
    have hwD : restrictedBoxInitCLM p w ∈ D.closedBox := by
      rw [D.mem_closedBox]
      intro j
      have hinit := ((D.mem_closedBox_snoc hlu).mp hw).1
      rw [D.mem_closedBox] at hinit
      simpa using hinit j
    have hf := (D.analyticNearClosedBox_iff.mp f.property)
      (restrictedBoxInitCLM p w) hwD
    change AnalyticAt ℝ
      ((f : RestrictedBoxSpace p → ℝ) ∘ restrictedBoxInitCLM p) w
    exact hf.compContinuousLinearMap (u := restrictedBoxInitCLM p)⟩

@[simp]
theorem RestrictedBox.pullbackSnoc_apply {p : ℕ} (D : RestrictedBox p)
    (l u : ℝ) (hlu : l < u)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (w : RestrictedBoxSpace (p + 1)) :
    (D.pullbackSnoc l u hlu f : RestrictedBoxSpace (p + 1) → ℝ) w =
      (f : RestrictedBoxSpace p → ℝ) (restrictedBoxInitCLM p w) :=
  rfl

/-- The retained offsets on the enlarged box. -/
def restrictedReclassifiedOffset {m p : ℕ} (D : RestrictedBox p)
    (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1)) :
    RestrictedRetainedOffsetIndex representative i →
      RestrictedBox.analyticNearClosedBoxSubalgebra (D.snoc R M hRM) :=
  fun k ↦ D.pullbackSnoc R M hRM (offset k.1)

@[simp]
theorem restrictedReclassifiedOffset_apply {m p : ℕ}
    (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedRetainedOffsetIndex representative i)
    (w : RestrictedBoxSpace (p + 1)) :
    (restrictedReclassifiedOffset D R M hRM representative offset i k :
        RestrictedBoxSpace (p + 1) → ℝ) w =
      (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p w) :=
  rfl

/-- A retained shifted argument agrees with its old shifted argument after
the source reclassification. -/
theorem restrictedAbelArgument_reclassified_retained
    {m p a : ℕ} (D : RestrictedBox p)
    (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedRetainedOffsetIndex representative i)
    (x : RestrictedSource m (p + 1) a) :
    restrictedAbelArgument
        (restrictedReclassifiedRepresentative representative i k)
        (restrictedReclassifiedOffset D R M hRM representative offset i k :
          RestrictedBoxSpace (p + 1) → ℝ) x =
      restrictedAbelArgument (representative k.1)
        (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedSourceReclassifyAt i x) := by
  have hw :
      (restrictedSourceReclassifyAt i x).1.2 =
        restrictedBoxInitCLM p x.1.2 := by
    funext j
    simp
  change x.1.1 (restrictedReclassifiedRepresentative representative i k) +
      (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p x.1.2) =
    (restrictedSourceReclassifyAt i x).1.1 (representative k.1) +
      (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedSourceReclassifyAt i x).1.2
  rw [← succAbove_restrictedReclassifiedRepresentative
    representative i k, restrictedSourceReclassifyAt_apply_succAbove, hw]

/-- The corresponding retained Abel jets also agree pointwise. -/
theorem restrictedAbelJet_reclassified_retained
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedRetainedOffsetIndex representative i) (r : ℕ)
    (x : RestrictedSource m (p + 1) a) :
    restrictedAbelJet A
        (restrictedReclassifiedRepresentative representative i k)
        (restrictedReclassifiedOffset D R M hRM representative offset i k :
          RestrictedBoxSpace (p + 1) → ℝ) r x =
      restrictedAbelJet A (representative k.1)
        (offset k.1 : RestrictedBoxSpace p → ℝ) r
        (restrictedSourceReclassifyAt i x) := by
  exact congrArg (iteratedDeriv r A)
    (restrictedAbelArgument_reclassified_retained
      D R M hRM representative offset i k x)

/-- Function-level form of the retained-jet evaluation identity. -/
theorem precomp_restrictedAbelJet_reclassified_retained
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedRetainedOffsetIndex representative i) (r : ℕ) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedAbelJet A (representative k.1)
          (offset k.1 : RestrictedBoxSpace p → ℝ) r) =
      restrictedAbelJet A
        (restrictedReclassifiedRepresentative representative i k)
        (restrictedReclassifiedOffset D R M hRM representative offset i k :
          RestrictedBoxSpace (p + 1) → ℝ) r := by
  funext x
  exact (restrictedAbelJet_reclassified_retained
    A D R M hRM representative offset i k r x).symm

/-- The shifted argument of a pivot label, now viewed purely as a function
of the enlarged bounded box. -/
def restrictedReclassifiedPivotArgument {m p : ℕ}
    {D : RestrictedBox p} (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedPivotOffsetIndex representative i) :
    RestrictedBoxSpace (p + 1) → ℝ :=
  fun w ↦ w (Fin.last p) +
    (offset k.1 : RestrictedBoxSpace p → ℝ) (restrictedBoxInitCLM p w)

/-- A pivot shifted argument after source reclassification is exactly the
new box-only argument. -/
theorem restrictedAbelArgument_reclassified_pivot
    {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedPivotOffsetIndex representative i)
    (x : RestrictedSource m (p + 1) a) :
    restrictedAbelArgument (representative k.1)
        (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedSourceReclassifyAt i x) =
      restrictedReclassifiedPivotArgument representative offset i k x.1.2 := by
  have hw :
      (restrictedSourceReclassifyAt i x).1.2 =
        restrictedBoxInitCLM p x.1.2 := by
    funext j
    simp
  change (restrictedSourceReclassifyAt i x).1.1 (representative k.1) +
      (offset k.1 : RestrictedBoxSpace p → ℝ)
        (restrictedSourceReclassifyAt i x).1.2 =
    x.1.2 (Fin.last p) + (offset k.1 : RestrictedBoxSpace p → ℝ)
      (restrictedBoxInitCLM p x.1.2)
  rw [k.2, restrictedSourceReclassifyAt_apply_pivot, hw]

/-- The pivot jet as a raw function of the enlarged box. -/
def restrictedReclassifiedPivotJet (A : ℝ → ℝ) {m p : ℕ}
    {D : RestrictedBox p} (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ) :
    RestrictedBoxSpace (p + 1) → ℝ :=
  fun w ↦ iteratedDeriv r A
    (restrictedReclassifiedPivotArgument representative offset i k w)

/-- The old pivot jet after source reclassification is its new box-only
form. -/
theorem restrictedAbelJet_reclassified_pivot
    (A : ℝ → ℝ) {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ)
    (x : RestrictedSource m (p + 1) a) :
    restrictedAbelJet A (representative k.1)
        (offset k.1 : RestrictedBoxSpace p → ℝ) r
        (restrictedSourceReclassifyAt i x) =
      restrictedReclassifiedPivotJet A representative offset i k r x.1.2 := by
  exact congrArg (iteratedDeriv r A)
    (restrictedAbelArgument_reclassified_pivot
      representative offset i k x)

/-- Positivity inherited from the old closed-domain hypothesis makes every
pivot jet analytic near the enlarged closed box. -/
theorem IsAbel.restrictedReclassifiedPivotJet_analyticNearClosedBox
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ) :
    (D.snoc R M hRM).AnalyticNearClosedBox
      (restrictedReclassifiedPivotJet A representative offset i k r) := by
  have harg : (D.snoc R M hRM).AnalyticNearClosedBox
      (restrictedReclassifiedPivotArgument representative offset i k) := by
    rw [(D.snoc R M hRM).analyticNearClosedBox_iff]
    have hlast : AnalyticOnNhd ℝ
        (fun w : RestrictedBoxSpace (p + 1) ↦ w (Fin.last p))
        (D.snoc R M hRM).closedBox :=
      (D.snoc R M hRM).analyticNearClosedBox_iff.mp
        ((D.snoc R M hRM).analyticNearClosedBox_apply (Fin.last p))
    have hoff : AnalyticOnNhd ℝ
        (fun w : RestrictedBoxSpace (p + 1) ↦
          (offset k.1 : RestrictedBoxSpace p → ℝ)
            (restrictedBoxInitCLM p w))
        (D.snoc R M hRM).closedBox :=
      (D.snoc R M hRM).analyticNearClosedBox_iff.mp
        (D.pullbackSnoc R M hRM (offset k.1)).property
    change AnalyticOnNhd ℝ
      ((fun w : RestrictedBoxSpace (p + 1) ↦ w (Fin.last p)) +
        fun w ↦ (offset k.1 : RestrictedBoxSpace p → ℝ)
          (restrictedBoxInitCLM p w))
      (D.snoc R M hRM).closedBox
    exact hlast.add hoff
  have hpos : MapsTo
      (restrictedReclassifiedPivotArgument representative offset i k)
      (D.snoc R M hRM).closedBox (Ioi 0) := by
    intro w hw
    let x : RestrictedSource m (p + 1) a :=
      (((fun _ ↦ R), w), fun _ ↦ 0)
    have hx : x ∈ restrictedBaseClosedDomain (D.snoc R M hRM) R := by
      exact ⟨fun _ ↦ le_rfl, hw⟩
    have hxOld : restrictedSourceReclassifyAt i x ∈
        restrictedBaseClosedDomain D R :=
      mapsTo_restrictedBaseClosedDomain_reclassifyAt
        D R M hRM i hx
    have hk := (hDomain hxOld).2 k.1
    have hargEq := restrictedAbelArgument_reclassified_pivot
      representative offset i k x
    change 0 < restrictedReclassifiedPivotArgument
      representative offset i k w
    rw [hargEq] at hk
    simpa only [x] using hk
  rw [(D.snoc R M hRM).analyticNearClosedBox_iff]
  change AnalyticOnNhd ℝ
    ((iteratedDeriv r A) ∘
      restrictedReclassifiedPivotArgument representative offset i k)
    (D.snoc R M hRM).closedBox
  rw [iteratedDeriv_eq_iterate]
  exact (hA.analytic.iterated_deriv r).comp
    ((D.snoc R M hRM).analyticNearClosedBox_iff.mp harg) hpos

/-- The pivot jet packaged as an allowed analytic coefficient of the enlarged
box. -/
def IsAbel.restrictedReclassifiedPivotJetCoefficient
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ) :
    RestrictedBox.analyticNearClosedBoxSubalgebra (D.snoc R M hRM) :=
  ⟨restrictedReclassifiedPivotJet A representative offset i k r,
    hA.restrictedReclassifiedPivotJet_analyticNearClosedBox
      D R M hRM representative offset i hDomain k r⟩

@[simp]
theorem IsAbel.restrictedReclassifiedPivotJetCoefficient_apply
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ)
    (w : RestrictedBoxSpace (p + 1)) :
    (hA.restrictedReclassifiedPivotJetCoefficient
        D R M hRM representative offset i hDomain k r :
      RestrictedBoxSpace (p + 1) → ℝ) w =
      restrictedReclassifiedPivotJet A representative offset i k r w :=
  rfl

/-- Function-level form of the pivot-jet identity, now landing among the
analytic coefficient pullbacks of the enlarged expression base. -/
theorem IsAbel.precomp_restrictedAbelJet_reclassified_pivot
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset)
    (k : RestrictedPivotOffsetIndex representative i) (r : ℕ) :
    functionPrecompAlgHom (restrictedSourceReclassifyAt (a := a) i)
        (restrictedAbelJet A (representative k.1)
          (offset k.1 : RestrictedBoxSpace p → ℝ) r) =
      restrictedBoxCoefficientPullback (m := m) (a := a)
        (hA.restrictedReclassifiedPivotJetCoefficient
          D R M hRM representative offset i hDomain k r :
            RestrictedBoxSpace (p + 1) → ℝ) := by
  funext x
  exact restrictedAbelJet_reclassified_pivot
    A representative offset i k r x

/-- The reclassified closed domain is admissible for the retained Abel-jet
family. -/
theorem restrictedBaseClosedDomain_subset_reclassifiedAbelJetDomain
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin (m + 1))
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) D R ⊆
        restrictedAbelJetDomain (a := a) D representative offset) :
    restrictedBaseClosedDomain (m := m) (a := a)
        (D.snoc R M hRM) R ⊆
      restrictedAbelJetDomain (a := a) (D.snoc R M hRM)
        (restrictedReclassifiedRepresentative representative i)
        (restrictedReclassifiedOffset
          D R M hRM representative offset i) := by
  intro x hx
  refine ⟨hx.2, ?_⟩
  intro k
  have hk :=
    (hDomain (mapsTo_restrictedBaseClosedDomain_reclassifyAt
      D R M hRM i hx)).2 k.1
  rw [restrictedAbelArgument_reclassified_retained
    D R M hRM representative offset i k x]
  exact hk

end AbelFormalization
