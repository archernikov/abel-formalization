import AbelFormalization.CharbonnelClosureInteriorRegularity
import AbelFormalization.KuratowskiUlamProduct

/-!
# Family-level meaning of Maxwell meagre component selection

Under WS5 and WS6, the component-selection formulation is exactly equivalent
to Maxwell--Servi closure-interior regularity.  The reverse implication is
vacuous: a meagre member has empty interior, so closure regularity contradicts
the assumed nonempty interior of its closure before a section is selected.

`KuratowskiUlamProduct` supplies the category/Fubini theorem used inside the
source proof.  The equivalences below make clear that this topological theorem
does not by itself prove component selection: what remains is precisely the
family-level closure-regularity argument using the weak-structure operations
and WS5.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Under WS5 and WS6, the finite-selection predicate is equivalent to its
direct family-level content: a meagre member cannot have closure with nonempty
interior. -/
theorem hasMaxwellMeagreClosureComponentSelection_iff_meagreClosureRegularity
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    HasMaxwellMeagreClosureComponentSelection C ↔
      (∀ {n : ℕ}, 0 < n →
        ∀ {A : Set (RealEuclidean n)}, A ∈ C n →
          IsMeagre A → interior (closure A) = ∅) := by
  constructor
  · intro hselection n hn A hA hmeagre
    have hregularity : CharbonnelClosureInteriorRegularity C :=
      charbonnelClosureInteriorRegularity_of_ws5_ws6_and_maxwellMeagreSelection
        hC hselection
    exact hregularity hn hA (IsMeagre.interior_eq_empty hmeagre)
  · intro hregularity n hn A hA hmeagre hclosure _N
    exact False.elim (hclosure (hregularity hn hA hmeagre))

/-- In a positive-arity o-minimal weak family, Maxwell's meagre component
selection predicate carries precisely the same information as closure
preserving empty interior. -/
theorem hasMaxwellMeagreClosureComponentSelection_iff_closureInteriorRegularity
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    HasMaxwellMeagreClosureComponentSelection C ↔
      CharbonnelClosureInteriorRegularity C := by
  constructor
  · exact
      charbonnelClosureInteriorRegularity_of_ws5_ws6_and_maxwellMeagreSelection
        hC
  · intro hregularity n hn A hA hmeagre hclosure _N
    exact False.elim
      (hclosure
        (hregularity hn hA (IsMeagre.interior_eq_empty hmeagre)))

end AbelFormalization
