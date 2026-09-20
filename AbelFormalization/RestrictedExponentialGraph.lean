import AbelFormalization.ExponentialAdjunctionOpenLocus
import AbelFormalization.RestrictedExponentialAdjunctionLocus
import AbelFormalization.RestrictedSourceLinearEquiv

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- The old restricted source domain before the final positive graph
coordinate is adjoined. -/
def restrictedBaseOpenDomain {m p a : ℕ} (D : RestrictedBox p) (R : ℝ) :
    Set (RestrictedSource m p a) :=
  {x | (∀ i, R < x.1.1 i) ∧ x.1.2 ∈ D.openBox}

/-- Express a system on a restricted source with one fresh auxiliary
coordinate in split product coordinates. -/
def restrictedSystemProductForm {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ) :
    RestrictedSource m p a × ℝ → Fin n → ℝ :=
  fun q i ↦ H i (restrictedSourceAppendAuxOne q.1 q.2)

@[simp]
theorem restrictedSystemProductForm_apply {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (q : RestrictedSource m p a × ℝ) (i : Fin n) :
    restrictedSystemProductForm H q i =
      H i (restrictedSourceAppendAuxOne q.1 q.2) := rfl

@[simp]
theorem restrictedSystemProductForm_projection {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (y : RestrictedSource m p (a + 1)) :
    restrictedSystemProductForm H (restrictedDenominatorProjection y) =
      fun i ↦ H i y := by
  funext i
  simp [restrictedSystemProductForm, restrictedDenominatorProjection]

/-- The graph determinant `J` written as a function on the unsplit
restricted source. -/
def restrictedExponentialAdjunctionJacobian {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a)) :
    RestrictedSource m p (a + 1) → ℝ :=
  fun y ↦ exponentialAdjunctionJacobian (restrictedSystemProductForm H) g basis
    (restrictedDenominatorProjection y)

/-- The logarithmic comparison `log Y - g` on the restricted source. -/
def restrictedExponentialGraphComparison {m p a : ℕ}
    (g : RestrictedSource m p a → ℝ) :
    RestrictedSource m p (a + 1) → ℝ :=
  fun y ↦ exponentialGraphComparison g (restrictedDenominatorProjection y)

@[simp]
theorem restrictedExponentialGraphComparison_appendAuxOne {m p a : ℕ}
    (g : RestrictedSource m p a → ℝ) (x : RestrictedSource m p a) (Y : ℝ) :
    restrictedExponentialGraphComparison g
        (restrictedSourceAppendAuxOne x Y) = Real.log Y - g x := by
  simp [restrictedExponentialGraphComparison, exponentialGraphComparison]

@[simp]
theorem restrictedExponentialAdjunctionJacobian_appendAuxOne {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (x : RestrictedSource m p a) (Y : ℝ) :
    restrictedExponentialAdjunctionJacobian H g basis
        (restrictedSourceAppendAuxOne x Y) =
      exponentialAdjunctionJacobian (restrictedSystemProductForm H) g basis (x, Y) := by
  simp [restrictedExponentialAdjunctionJacobian]


theorem mem_restrictedExponentialAdjunctionCurve_iff_productForm {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (y : RestrictedSource m p (a + 1)) :
    y ∈ restrictedExponentialAdjunctionCurve H D R
        (restrictedExponentialAdjunctionJacobian H g basis) ↔
      restrictedDenominatorProjection y ∈
        exponentialAdjunctionOpenLocus (restrictedBaseOpenDomain D R)
          (restrictedSystemProductForm H) g basis := by
  rw [mem_restrictedExponentialAdjunctionCurve_iff]
  simp only [exponentialAdjunctionOpenLocus, restrictedBaseOpenDomain,
    restrictedExponentialAdjunctionJacobian, restrictedDenominatorProjection,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hH, ⟨hs, hw, hY⟩, hJ⟩
    exact ⟨⟨hs, hw⟩,
      funext fun i ↦ by
        change H i (restrictedSourceAppendAuxOne
          (restrictedSourceDropAux 1 y)
          (restrictedAuxCoordinate (Fin.last a) y)) = 0
        rw [restrictedSourceAppendAuxOne_projection]
        exact hH i,
      hY, hJ⟩
  · rintro ⟨⟨hs, hw⟩, hH, hY, hJ⟩
    exact ⟨fun i ↦ by
      have := congrFun hH i
      change H i (restrictedSourceAppendAuxOne
        (restrictedSourceDropAux 1 y)
        (restrictedAuxCoordinate (Fin.last a) y)) = 0 at this
      simpa using this,
      ⟨hs, hw, hY⟩, hJ⟩


/-- Substitute the exponential graph into a system on the enlarged
restricted source. -/
def restrictedExponentialGraphSubstitution {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ) :
    RestrictedSource m p a → Fin n → ℝ :=
  exponentialGraphSubstitution (restrictedSystemProductForm H) g

@[simp]
theorem restrictedExponentialGraphSubstitution_apply {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (g : RestrictedSource m p a → ℝ) (x : RestrictedSource m p a) :
    restrictedExponentialGraphSubstitution H g x =
      fun i ↦ H i (restrictedSourceAppendAuxOne x (Real.exp (g x))) := by
  rfl

/-- Concrete restricted-source form of the canonical correspondence between
original regular zeros and comparison zeros on `V`. -/
def restrictedRegularZeroSetEquivComparisonZero {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (hH : ∀ x, DifferentiableAt ℝ (restrictedSystemProductForm H)
      (x, Real.exp (g x)))
    (hg : Differentiable ℝ g) :
    regularZeroSet (restrictedBaseOpenDomain D R)
        (restrictedExponentialGraphSubstitution H g) ≃
      {y : RestrictedSource m p (a + 1) |
        y ∈ restrictedExponentialAdjunctionCurve H D R
          (restrictedExponentialAdjunctionJacobian H g basis) ∧
        restrictedExponentialGraphComparison g y = 0} where
  toFun x := ⟨restrictedSourceAppendAuxOne x (Real.exp (g x)), by
    have hgeneric :=
      (mem_openLocus_and_comparison_zero_iff_regularZero
        (restrictedBaseOpenDomain D R) (restrictedSystemProductForm H) g basis
        x (Real.exp (g x)) (hH x) (hg x)).mpr ⟨rfl, x.property⟩
    refine ⟨(mem_restrictedExponentialAdjunctionCurve_iff_productForm
      H D R g basis _).mpr ?_, ?_⟩
    · simpa using hgeneric.1
    · simp [restrictedExponentialGraphComparison]
    ⟩
  invFun y := ⟨restrictedSourceDropAux 1 y, by
    have hgenericLocus :=
      (mem_restrictedExponentialAdjunctionCurve_iff_productForm
        H D R g basis y).mp y.property.1
    have hgenericComparison : exponentialGraphComparison g
        (restrictedSourceDropAux 1
            (y : RestrictedSource m p (a + 1)),
          restrictedAuxCoordinate (Fin.last a)
            (y : RestrictedSource m p (a + 1))) = 0 := by
      exact y.property.2
    exact ((mem_openLocus_and_comparison_zero_iff_regularZero
      (restrictedBaseOpenDomain D R) (restrictedSystemProductForm H) g basis
      (restrictedSourceDropAux 1 (y : RestrictedSource m p (a + 1)))
      (restrictedAuxCoordinate (Fin.last a)
        (y : RestrictedSource m p (a + 1)))
      (hH (restrictedSourceDropAux 1
        (y : RestrictedSource m p (a + 1))))
      (hg (restrictedSourceDropAux 1
        (y : RestrictedSource m p (a + 1))))).mp
        ⟨hgenericLocus, hgenericComparison⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    exact restrictedSourceDropAux_appendAuxOne
      (x : RestrictedSource m p a) (Real.exp (g x))
  right_inv y := by
    apply Subtype.ext
    change restrictedSourceAppendAuxOne
        (restrictedSourceDropAux 1
          (y : RestrictedSource m p (a + 1)))
        (Real.exp (g (restrictedSourceDropAux 1
          (y : RestrictedSource m p (a + 1))))) =
      (y : RestrictedSource m p (a + 1))
    have hgenericLocus :=
      (mem_restrictedExponentialAdjunctionCurve_iff_productForm
        H D R g basis y).mp y.property.1
    have hY : restrictedAuxCoordinate (Fin.last a)
        (y : RestrictedSource m p (a + 1)) =
          Real.exp (g (restrictedSourceDropAux 1
            (y : RestrictedSource m p (a + 1)))) :=
      (exponentialGraphComparison_eq_zero_iff g
        hgenericLocus.2.2.1).mp y.property.2
    rw [← hY]
    exact restrictedSourceAppendAuxOne_projection
      (y : RestrictedSource m p (a + 1))

/-- Domain-local form of the restricted exponential-adjunction
correspondence.  This is the form used for Abel expressions, whose chosen
total representatives need only be differentiable on the common positive
jet domain. -/
def restrictedRegularZeroSetEquivComparisonZeroOn {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (hH : ∀ x ∈ restrictedBaseOpenDomain D R,
      DifferentiableAt ℝ (restrictedSystemProductForm H)
        (x, Real.exp (g x)))
    (hg : ∀ x ∈ restrictedBaseOpenDomain D R,
      DifferentiableAt ℝ g x) :
    regularZeroSet (restrictedBaseOpenDomain D R)
        (restrictedExponentialGraphSubstitution H g) ≃
      {y : RestrictedSource m p (a + 1) |
        y ∈ restrictedExponentialAdjunctionCurve H D R
          (restrictedExponentialAdjunctionJacobian H g basis) ∧
        restrictedExponentialGraphComparison g y = 0} where
  toFun x := ⟨restrictedSourceAppendAuxOne x (Real.exp (g x)), by
    have hgeneric :=
      (mem_openLocus_and_comparison_zero_iff_regularZero
        (restrictedBaseOpenDomain D R) (restrictedSystemProductForm H) g basis
        x (Real.exp (g x)) (hH x x.property.1) (hg x x.property.1)).mpr
          ⟨rfl, x.property⟩
    refine ⟨(mem_restrictedExponentialAdjunctionCurve_iff_productForm
      H D R g basis _).mpr ?_, ?_⟩
    · simpa using hgeneric.1
    · simp [restrictedExponentialGraphComparison]
    ⟩
  invFun y := ⟨restrictedSourceDropAux 1 y, by
    have hgenericLocus :=
      (mem_restrictedExponentialAdjunctionCurve_iff_productForm
        H D R g basis y).mp y.property.1
    have hgenericComparison : exponentialGraphComparison g
        (restrictedSourceDropAux 1
            (y : RestrictedSource m p (a + 1)),
          restrictedAuxCoordinate (Fin.last a)
            (y : RestrictedSource m p (a + 1))) = 0 := by
      exact y.property.2
    exact ((mem_openLocus_and_comparison_zero_iff_regularZero
      (restrictedBaseOpenDomain D R) (restrictedSystemProductForm H) g basis
      (restrictedSourceDropAux 1 (y : RestrictedSource m p (a + 1)))
      (restrictedAuxCoordinate (Fin.last a)
        (y : RestrictedSource m p (a + 1)))
      (hH (restrictedSourceDropAux 1
        (y : RestrictedSource m p (a + 1))) hgenericLocus.1)
      (hg (restrictedSourceDropAux 1
        (y : RestrictedSource m p (a + 1))) hgenericLocus.1)).mp
        ⟨hgenericLocus, hgenericComparison⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    exact restrictedSourceDropAux_appendAuxOne
      (x : RestrictedSource m p a) (Real.exp (g x))
  right_inv y := by
    apply Subtype.ext
    change restrictedSourceAppendAuxOne
        (restrictedSourceDropAux 1
          (y : RestrictedSource m p (a + 1)))
        (Real.exp (g (restrictedSourceDropAux 1
          (y : RestrictedSource m p (a + 1))))) =
      (y : RestrictedSource m p (a + 1))
    have hgenericLocus :=
      (mem_restrictedExponentialAdjunctionCurve_iff_productForm
        H D R g basis y).mp y.property.1
    have hY : restrictedAuxCoordinate (Fin.last a)
        (y : RestrictedSource m p (a + 1)) =
          Real.exp (g (restrictedSourceDropAux 1
            (y : RestrictedSource m p (a + 1)))) :=
      (exponentialGraphComparison_eq_zero_iff g
        hgenericLocus.2.2.1).mp y.property.2
    rw [← hY]
    exact restrictedSourceAppendAuxOne_projection
      (y : RestrictedSource m p (a + 1))

end AbelFormalization
