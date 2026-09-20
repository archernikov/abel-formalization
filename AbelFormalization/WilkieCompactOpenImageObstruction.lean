import AbelFormalization.WilkieFixedMinorConnectedInterval

/-!
# Compact-open obstruction for an arbitrary coordinate minor

Wilkie 2.9's finite-visible-projection case ultimately applies an implicit
chart to a *different* projection: it retains the coordinates complementary
to any chosen maximal Jacobian minor.  A compact connected fiber component
cannot have a nonempty image open in that noncompact coordinate space.  The
topological obstruction below is independent of the choice of columns.
The local inverse-function chart that supplies openness is separate.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A continuous image of a nonempty compact set cannot be open in a
preconnected noncompact Hausdorff space. -/
theorem compact_nonempty_image_not_open
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    [T2Space T] [PreconnectedSpace T] [NoncompactSpace T]
    {p : E → T} (hp : Continuous p) {Y : Set E}
    (hYcompact : IsCompact Y) (hYnonempty : Y.Nonempty) :
    ¬ IsOpen (p '' Y) := by
  intro hopen
  have hcompact : IsCompact (p '' Y) := hYcompact.image hp
  have hnonempty : (p '' Y).Nonempty := by
    obtain ⟨y, hyY⟩ := hYnonempty
    exact ⟨p y, ⟨y, hyY, rfl⟩⟩
  have huniv : p '' Y = univ :=
    IsClopen.eq_univ ⟨hcompact.isClosed, hopen⟩ hnonempty
  exact hcompact.ne_univ huniv

/-- Once an arbitrary fixed-minor implicit chart makes the complementary
coordinate image open whenever the minor stays nonzero, compactness forces
that same minor to vanish on the component. -/
theorem fixed_minor_zero_of_compact_component_and_open_chart
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    [T2Space T] [PreconnectedSpace T] [NoncompactSpace T]
    {p : E → T} (hp : Continuous p) {Y : Set E}
    (hYcompact : IsCompact Y) (hYnonempty : Y.Nonempty)
    {d : E → ℝ}
    (hopen_if_nonzero : (∀ y ∈ Y, d y ≠ 0) → IsOpen (p '' Y)) :
    ∃ z ∈ Y, d z = 0 := by
  by_contra hmissing
  have hnonzero : ∀ y ∈ Y, d y ≠ 0 := by
    intro y hyY hzero
    exact hmissing ⟨y, hyY, hzero⟩
  exact (compact_nonempty_image_not_open hp hYcompact hYnonempty)
    (hopen_if_nonzero hnonzero)

end AbelFormalization
