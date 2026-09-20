import AbelFormalization.ClosedDenominatorGraph

/-!
# Finite components from finite lifted minimizers

This file isolates the topological choice argument used when critical points
live in an auxiliary space.  A continuous real-valued function with compact
sublevel sets has a minimum on every connected component.  If every such
minimum is the base point of an auxiliary lift, then choosing one lift on
each component gives an injection from the connected-component quotient to
the auxiliary type.

The auxiliary type can, for example, be a finite subtype of an augmented
Lagrange critical system.  No differential structure is used here.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- If every connected component contains the base point of an auxiliary
lift, one can choose those lifts injectively by components. -/
theorem exists_injective_connectedComponents_to_lifts
    {X Y : Type*} [TopologicalSpace X]
    (base : Y → X)
    (hmeet : ∀ x : X, ∃ y : Y, base y ∈ connectedComponent x) :
    ∃ pick : ConnectedComponents X → Y, Function.Injective pick := by
  classical
  let representative : ConnectedComponents X → X := fun component ↦
    Classical.choose (ConnectedComponents.surjective_coe component)
  have hrepresentative : ∀ component : ConnectedComponents X,
      (representative component : ConnectedComponents X) = component := by
    intro component
    exact Classical.choose_spec (ConnectedComponents.surjective_coe component)
  have hlift : ∀ component : ConnectedComponents X,
      ∃ y : Y, base y ∈ connectedComponent (representative component) := by
    intro component
    exact hmeet (representative component)
  let pick : ConnectedComponents X → Y := fun component ↦
    Classical.choose (hlift component)
  have hpick : ∀ component : ConnectedComponents X,
      base (pick component) ∈
        connectedComponent (representative component) := by
    intro component
    exact Classical.choose_spec (hlift component)
  refine ⟨pick, ?_⟩
  intro component component' heq
  have hbase : ∀ c : ConnectedComponents X,
      (base (pick c) : ConnectedComponents X) = c := by
    intro c
    exact (ConnectedComponents.coe_eq_coe'.2 (hpick c)).trans
      (hrepresentative c)
  calc
    component = (base (pick component) : ConnectedComponents X) :=
      (hbase component).symm
    _ = (base (pick component') : ConnectedComponents X) := by rw [heq]
    _ = component' := hbase component'

/-- A finite auxiliary type meeting every connected component through its
base map forces the connected-component quotient to be finite. -/
theorem finite_connectedComponents_of_finite_lifts
    {X Y : Type*} [TopologicalSpace X] [Finite Y]
    (base : Y → X)
    (hmeet : ∀ x : X, ∃ y : Y, base y ∈ connectedComponent x) :
    Finite (ConnectedComponents X) := by
  obtain ⟨pick, hpick⟩ :=
    exists_injective_connectedComponents_to_lifts base hmeet
  exact Finite.of_injective pick hpick

/-- Proper componentwise minimizers may be lifted into any finite auxiliary
type.  The chosen lifts give an injection of connected components into that
type. -/
theorem finite_connectedComponents_of_finite_lifted_componentMinimizers
    {X Y : Type*} [TopologicalSpace X] [Finite Y]
    (f : X → ℝ) (hf : Continuous f)
    (hcompact : ∀ r : ℝ, IsCompact {x | f x ≤ r})
    (base : Y → X)
    (hlift : ∀ x : X, x ∈ componentMinimizers f →
      ∃ y : Y, base y = x) :
    Finite (ConnectedComponents X) := by
  apply finite_connectedComponents_of_finite_lifts base
  intro x
  obtain ⟨y, hycomponent, hymin⟩ :=
    exists_componentMinimizer_of_compact_sublevel f hf hcompact x
  obtain ⟨z, hz⟩ := hlift y hymin
  refine ⟨z, ?_⟩
  simpa only [hz] using hycomponent

/-- A clopen subspace has no more connected components than its ambient
space.  In particular, finiteness of ambient components passes to every
clopen subtype. -/
theorem finite_connectedComponents_clopen_subtype
    {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    {S : Set X} (hS : IsClopen S) :
    Finite (ConnectedComponents S) := by
  let inclusion : ConnectedComponents S → ConnectedComponents X :=
    (continuous_subtype_val : Continuous (Subtype.val : S → X)).connectedComponentsMap
  apply Finite.of_injective inclusion
  intro component component' heq
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe component'
  have hambient : (x : X) ∈ connectedComponent (y : X) := by
    apply ConnectedComponents.coe_eq_coe'.mp
    simpa only [inclusion, Continuous.connectedComponentsMap_mk] using heq
  have hwithin : (x : X) ∈ connectedComponentIn S (y : X) := by
    rw [hS.connectedComponentIn_eq y.property]
    exact hambient
  rw [connectedComponentIn_eq_image y.property] at hwithin
  obtain ⟨x', hx'component, hx'value⟩ := hwithin
  have hx'eq : x' = x := Subtype.ext hx'value
  subst x'
  exact ConnectedComponents.coe_eq_coe'.mpr hx'component

end AbelFormalization
