import AbelFormalization.CriticalSystemRegularity

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- A subset meeting each connected component in at most one point has
cardinality at most the number of connected components.  This quantitative
form is the counting step in Lion's Rolle lemma. -/
theorem enatCard_le_connectedComponents_of_component_unique
    {X : Type*} [TopologicalSpace X] {Z : Set X}
    (hunique : ∀ (x y : Z),
      ConnectedComponents.mk (x : X) =
        ConnectedComponents.mk (y : X) → x = y) :
    ENat.card Z ≤ ENat.card (ConnectedComponents X) := by
  apply ENat.card_le_card_of_injective
  intro x y hxy
  exact hunique x y hxy

/-- A set meeting each connected component in at most one point is finite
when the ambient space has finitely many connected components. -/
theorem Set.Finite.of_finite_connectedComponents
    {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    {Z : Set X}
    (hunique : ∀ (x : Z) (y : Z),
      (x : ConnectedComponents X) = y → x = y) :
    Z.Finite := by
  apply Set.Finite.of_finite_image
    (f := fun x : X ↦ (x : ConnectedComponents X)) (Set.toFinite _)
  intro x hx y hy hxy
  exact congrArg Subtype.val (hunique ⟨x, hx⟩ ⟨y, hy⟩ hxy)

/-- Connected-component membership is the form of the preceding uniqueness
hypothesis usually produced by Rolle's theorem. -/
theorem Set.Finite.of_finite_connectedComponents_of_component_unique
    {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    {Z : Set X}
    (hunique : ∀ (x : Z) (y : Z),
      (y : X) ∈ connectedComponent (x : X) → x = y) :
    Z.Finite := by
  apply Set.Finite.of_finite_connectedComponents
  intro x y hxy
  apply hunique x y
  exact (ConnectedComponents.coe_eq_coe' (x := (y : X)) (y := (x : X))).mp hxy.symm

/-- Ambient points are finite when their lifts to a constraint locus meet
each connected component at most once. -/
theorem finite_ambient_of_component_unique_lifts
    {E : Type*} [TopologicalSpace E] {M Z : Set E}
    [Finite (ConnectedComponents M)]
    (hZM : Z ⊆ M)
    (hunique : ∀ (x : Z) (y : Z),
      (⟨y, hZM y.property⟩ : M) ∈
          connectedComponent (⟨x, hZM x.property⟩ : M) →
        x = y) :
    Z.Finite := by
  let ZM : Set M := {x | (x : E) ∈ Z}
  have hZMfinite : ZM.Finite := by
    apply Set.Finite.of_finite_connectedComponents_of_component_unique
    intro x y hcomponent
    have hcomponent' :
        (⟨(y : E), hZM y.property⟩ : M) ∈
          connectedComponent (⟨(x : E), hZM x.property⟩ : M) := by
      simpa only [Subtype.coe_eta] using hcomponent
    have hxyZ : (⟨(x : E), x.property⟩ : Z) =
        (⟨(y : E), y.property⟩ : Z) :=
      hunique ⟨x, x.property⟩ ⟨y, y.property⟩ hcomponent'
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Z ↦ (z : E)) hxyZ
  have himage : ((fun x : M ↦ (x : E)) '' ZM).Finite := hZMfinite.image _
  have himage_eq : (fun x : M ↦ (x : E)) '' ZM = Z := by
    ext x
    constructor
    · rintro ⟨y, hyZ, rfl⟩
      exact hyZ
    · intro hxZ
      exact ⟨⟨x, hZM hxZ⟩, hxZ, rfl⟩
  rwa [himage_eq] at himage

end AbelFormalization
