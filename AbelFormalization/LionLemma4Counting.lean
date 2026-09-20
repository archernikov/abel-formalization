import AbelFormalization.LionLemma4SectionAssembly
import AbelFormalization.LionTheorem7Induction

/-!
# The counting consequence of Lion's Lemma 4

The section assembly gives a finite family of `p`-dimensional leaves meeting
every component of a good fiber.  This file feeds those actual leaves into
the finite-section counting theorem used by Lion's Theorem 7' induction.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- On a good target, cardinal bounds for the fibers of the finitely many
section leaves add up to a bound for the connected components of the
original fiber. -/
theorem enatCard_connectedComponents_le_sum_selectedCriticalSections
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hselection :
      L.HasCriticalTraceRegularCoefficientSelection g center height)
    (t : RealEuclidean p)
    (ht : t ∈ L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)
    (bound : CriticalCoefficientSelection n q p → ℕ)
    (hbound : ∀ selection : CriticalCoefficientSelection n q p,
      ENat.card
        ((L.selectedCriticalSectionLeaf
          hG hsmooth hderiv g hg center hheight hdim selection).fiber g t) ≤
            bound selection) :
    ENat.card (ConnectedComponents (L.fiber g t)) ≤
      ∑ selection : CriticalCoefficientSelection n q p, bound selection := by
  let Point : CriticalCoefficientSelection n q p → Type := fun selection ↦
    (L.selectedCriticalSectionLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).fiber g t
  let embed : ∀ selection, Point selection → L.fiber g t :=
    fun selection z ↦
      ⟨z, L.selectedCriticalSectionLeaf_carrier_subset
        hG hsmooth hderiv g hg center hheight hdim selection z.property.1,
          z.property.2⟩
  have hmeet : ∀ x : L.fiber g t,
      ∃ selection, ∃ z : Point selection,
        embed selection z ∈ connectedComponent x := by
    intro x
    obtain ⟨selection, y, hycomponent, hysection⟩ :=
      L.exists_selectedCriticalSectionLeaf_point_in_connectedComponent_of_mem_good
        hG hsmooth hderiv g hg center hheight hdim hselection t ht x
    let z : Point selection :=
      ⟨(y : RealEuclidean n), hysection, y.property.2⟩
    refine ⟨selection, z, ?_⟩
    simpa only [embed, z] using hycomponent
  apply enatCard_connectedComponents_le_sum_of_finite_sections
    Point embed hmeet bound
  intro selection
  simpa only [Point] using hbound selection

/-- Component-counting form used by the recursive proof of Theorem 7'.
It is enough to bound the connected components of each section fiber: choose
one representative of every section component and include it into the
original fiber. -/
theorem enatCard_connectedComponents_le_sum_selectedCriticalSectionComponents
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hselection :
      L.HasCriticalTraceRegularCoefficientSelection g center height)
    (t : RealEuclidean p)
    (ht : t ∈ L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)
    (bound : CriticalCoefficientSelection n q p → ℕ)
    (hbound : ∀ selection : CriticalCoefficientSelection n q p,
      ENat.card
        (ConnectedComponents
          ((L.selectedCriticalSectionLeaf
            hG hsmooth hderiv g hg center hheight hdim selection).fiber g t)) ≤
              bound selection) :
    ENat.card (ConnectedComponents (L.fiber g t)) ≤
      ∑ selection : CriticalCoefficientSelection n q p, bound selection := by
  let K : CriticalCoefficientSelection n q p →
      LionCarpetedLeaf G n (n - p) := fun selection ↦
    L.selectedCriticalSectionLeaf
      hG hsmooth hderiv g hg center hheight hdim selection
  let Point : CriticalCoefficientSelection n q p → Type := fun selection ↦
    ConnectedComponents ((K selection).fiber g t)
  let representative : ∀ selection, Point selection →
      (K selection).fiber g t := fun _selection ↦
    Function.surjInv ConnectedComponents.surjective_coe
  let embed : ∀ selection, Point selection → L.fiber g t :=
    fun selection component ↦
      ⟨representative selection component,
        L.selectedCriticalSectionLeaf_carrier_subset
          hG hsmooth hderiv g hg center hheight hdim selection
            (representative selection component).property.1,
        (representative selection component).property.2⟩
  have hmeet : ∀ x : L.fiber g t,
      ∃ selection, ∃ component : Point selection,
        embed selection component ∈ connectedComponent x := by
    intro x
    obtain ⟨selection, y, hycomponent, hysection⟩ :=
      L.exists_selectedCriticalSectionLeaf_point_in_connectedComponent_of_mem_good
        hG hsmooth hderiv g hg center hheight hdim hselection t ht x
    let z : (K selection).fiber g t :=
      ⟨y, hysection, y.property.2⟩
    let component : Point selection := ConnectedComponents.mk z
    let inclusion : (K selection).fiber g t → L.fiber g t := fun w ↦
      ⟨w,
        L.selectedCriticalSectionLeaf_carrier_subset
          hG hsmooth hderiv g hg center hheight hdim selection w.property.1,
        w.property.2⟩
    have hinclusion : Continuous inclusion :=
      Continuous.subtype_mk continuous_subtype_val _
    have hrepresentative : representative selection component ∈
        connectedComponent z := by
      apply ConnectedComponents.coe_eq_coe'.mp
      simpa only [representative, component] using
        (Function.surjInv_eq
          ConnectedComponents.surjective_coe component)
    have hparent : inclusion (representative selection component) ∈
        connectedComponent (inclusion z) :=
      hinclusion.mapsTo_connectedComponent z hrepresentative
    refine ⟨selection, component, ?_⟩
    apply ConnectedComponents.coe_eq_coe'.mp
    exact (ConnectedComponents.coe_eq_coe'.mpr hparent).trans
      (ConnectedComponents.coe_eq_coe'.mpr hycomponent)
  apply enatCard_connectedComponents_le_sum_of_finite_sections
    Point embed hmeet bound
  intro selection
  simpa only [Point, K] using hbound selection

end LionCarpetedLeaf

end AbelFormalization
