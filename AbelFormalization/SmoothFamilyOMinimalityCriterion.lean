import AbelFormalization.Statement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Formal reductions for the smooth-family o-minimality criterion

This scratch module contains only the parts of the last o-minimality step that
follow from current mathlib.  In particular it does not postulate Lion's
uniform-fiber theorem or the Karpinski--Macintyre complement theorem.

The first group of lemmas records the elementary identities used to show that
projections of single zero sets are closed under intersections, unions, and
products.  The second group supplies the connected-component inequality used
for projections.  The final group gives the exact first-order reduct from an
o-minimal expansion to `AbelFormalization.OMinimal`.
-/

set_option autoImplicit false

noncomputable section

namespace AbelFormalization

open FirstOrder
open FirstOrder.Language

/-! ## Projections of one real zero set -/

/-- The projection to `X` of the zero set of a real-valued function on
`X × Z`, written in curried form. -/
def projectedZeroSet {X Z : Type*} (f : X → Z → ℝ) : Set X :=
  {x | ∃ z, f x z = 0}

/-- Two projected zero sets with the same visible variables can be intersected
by adding squares. -/
theorem projectedZeroSet_inter {X Z W : Type*}
    (f : X → Z → ℝ) (g : X → W → ℝ) :
    projectedZeroSet f ∩ projectedZeroSet g =
      projectedZeroSet (fun x (zw : Z × W) ↦ f x zw.1 ^ 2 + g x zw.2 ^ 2) := by
  ext x
  change ((∃ z, f x z = 0) ∧ ∃ w, g x w = 0) ↔
    ∃ zw : Z × W, f x zw.1 ^ 2 + g x zw.2 ^ 2 = 0
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
    exact ⟨(z, w), sq_add_sq_eq_zero.mpr ⟨hz, hw⟩⟩
  · rintro ⟨⟨z, w⟩, hzw⟩
    exact ⟨⟨z, (sq_add_sq_eq_zero.mp hzw).1⟩,
      ⟨w, (sq_add_sq_eq_zero.mp hzw).2⟩⟩

/-- Projected zero sets can be united by multiplying their equations.  The
witness types are inhabited, as are all spaces `Fin q → ℝ` occurring in the
manuscript, including `q = 0`. -/
theorem projectedZeroSet_union {X Z W : Type*} [Inhabited Z] [Inhabited W]
    (f : X → Z → ℝ) (g : X → W → ℝ) :
    projectedZeroSet f ∪ projectedZeroSet g =
      projectedZeroSet (fun x (zw : Z × W) ↦ f x zw.1 * g x zw.2) := by
  ext x
  change ((∃ z, f x z = 0) ∨ ∃ w, g x w = 0) ↔
    ∃ zw : Z × W, f x zw.1 * g x zw.2 = 0
  constructor
  · rintro (⟨z, hz⟩ | ⟨w, hw⟩)
    · exact ⟨(z, default), mul_eq_zero.mpr (Or.inl hz)⟩
    · exact ⟨(default, w), mul_eq_zero.mpr (Or.inr hw)⟩
  · rintro ⟨⟨z, w⟩, hzw⟩
    rcases mul_eq_zero.mp hzw with hz | hw
    · exact Or.inl ⟨z, hz⟩
    · exact Or.inr ⟨w, hw⟩

/-- Products of projected zero sets are represented by a sum of squares. -/
theorem projectedZeroSet_prod {X Y Z W : Type*}
    (f : X → Z → ℝ) (g : Y → W → ℝ) :
    projectedZeroSet f ×ˢ projectedZeroSet g =
      projectedZeroSet
        (fun (xy : X × Y) (zw : Z × W) ↦
          f xy.1 zw.1 ^ 2 + g xy.2 zw.2 ^ 2) := by
  ext xy
  change ((∃ z, f xy.1 z = 0) ∧ ∃ w, g xy.2 w = 0) ↔
    ∃ zw : Z × W, f xy.1 zw.1 ^ 2 + g xy.2 zw.2 ^ 2 = 0
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
    exact ⟨(z, w), sq_add_sq_eq_zero.mpr ⟨hz, hw⟩⟩
  · rintro ⟨⟨z, w⟩, hzw⟩
    exact ⟨⟨z, (sq_add_sq_eq_zero.mp hzw).1⟩,
      ⟨w, (sq_add_sq_eq_zero.mp hzw).2⟩⟩

/-- Pulling back a projected zero set only composes its defining equation in
the visible variables. -/
theorem preimage_projectedZeroSet {X Y Z : Type*}
    (e : Y → X) (f : X → Z → ℝ) :
    e ⁻¹' projectedZeroSet f = projectedZeroSet (fun y z ↦ f (e y) z) := by
  rfl

/-- The zero set of a continuous real-valued function is closed. -/
theorem isClosed_zeroSet {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) : IsClosed {x | f x = 0} := by
  exact isClosed_singleton.preimage hf

/-! ## Connected components and continuous projections -/

/-- A continuous surjection cannot increase the extended-natural number of
connected components.  Using `ENat.card`, rather than `Nat.card`, keeps the
statement honest when either component space is infinite. -/
theorem enatCard_connectedComponents_le_of_continuous_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    ENat.card (ConnectedComponents Y) ≤ ENat.card (ConnectedComponents X) := by
  apply ENat.card_le_card_of_injective
  exact Function.injective_surjInv
    (hf.connectedComponentsMap_surjective hsurj)

/-! ## The final first-order reduct -/

/-- Every member of a proposed unary set family has the decomposition used by
the project's o-minimality definition. -/
def HasUnaryPieceDecomposition (T : Set (Set ℝ)) : Prop :=
  ∀ s ∈ T, ∃ (n : ℕ) (pieces : Fin n → UnaryPiece),
    s = ⋃ i, (pieces i).carrier

/-- The direct set-family endpoint.  The nontrivial model-theoretic bridge is
the second hypothesis: it must be proved by induction on Abel-language
formulas from closure of the ambient set family and membership of the graphs
of the language symbols. -/
theorem oMinimal_of_unarySetFamily
    (A : ℝ → ℝ) (T : Set (Set ℝ))
    (hpieces : HasUnaryPieceDecomposition T)
    (hdef : ∀ s : Set ℝ, UnaryDefinable A s → s ∈ T) : OMinimal A := by
  intro s hs
  exact hpieces s (hdef s hs)

/-- Unary definability in an explicitly supplied structure.  Keeping the
structure as data avoids a global typeclass instance for an auxiliary
language. -/
def FirstOrderUnaryDefinable (L : FirstOrder.Language)
    (struc : L.Structure ℝ) (s : Set ℝ) : Prop :=
  letI := struc
  (Set.univ : Set ℝ).Definable₁ L s

/-- O-minimality for an arbitrary first-order structure on the reals, stated
with exactly the same unary pieces as `OMinimal`. -/
def FirstOrderOMinimal (L : FirstOrder.Language)
    (struc : L.Structure ℝ) : Prop :=
  ∀ s : Set ℝ, FirstOrderUnaryDefinable L struc s →
    ∃ (n : ℕ) (pieces : Fin n → UnaryPiece),
      s = ⋃ i, (pieces i).carrier

/-- Definability transfers from the Abel language to any genuine expansion of
its concrete structure. -/
theorem firstOrderUnaryDefinable_of_expansion
    (A : ℝ → ℝ) (L : FirstOrder.Language) (struc : L.Structure ℝ)
    (map : abelLanguage →ᴸ L)
    (hmap : @FirstOrder.Language.LHom.IsExpansionOn
      abelLanguage L map ℝ (abelStructure A) struc)
    {s : Set ℝ} (hs : UnaryDefinable A s) :
    FirstOrderUnaryDefinable L struc s := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  let _ : L.Structure ℝ := struc
  let _ : map.IsExpansionOn ℝ := hmap
  change (Set.univ : Set ℝ).Definable₁ abelLanguage s at hs
  change (Set.univ : Set ℝ).Definable₁ L s
  unfold Set.Definable₁ at hs ⊢
  exact hs.map_expansion map

/-- The unconditional final reduct theorem.  A formalized complement theorem
may provide the auxiliary o-minimal structure; once it also supplies the
language map and its interpretation laws, no further model theory is needed
to obtain the project's exact `OMinimal A` target. -/
theorem oMinimal_of_firstOrderExpansion
    (A : ℝ → ℝ) (L : FirstOrder.Language) (struc : L.Structure ℝ)
    (map : abelLanguage →ᴸ L)
    (hmap : @FirstOrder.Language.LHom.IsExpansionOn
      abelLanguage L map ℝ (abelStructure A) struc)
    (hL : FirstOrderOMinimal L struc) : OMinimal A := by
  intro s hs
  exact hL s
    (firstOrderUnaryDefinable_of_expansion A L struc map hmap hs)

/-- A convenient exact package for the output needed from the geometric and
complement-theorem stages.  This is an interface, not an assertion that such
an envelope exists. -/
structure OMinimalExpansionEnvelope (A : ℝ → ℝ) where
  language : FirstOrder.Language
  struc : language.Structure ℝ
  map : abelLanguage →ᴸ language
  isExpansion : @FirstOrder.Language.LHom.IsExpansionOn
    abelLanguage language map ℝ (abelStructure A) struc
  oMinimal : FirstOrderOMinimal language struc

/-- Eliminating the explicit envelope gives the exact project conclusion. -/
theorem OMinimalExpansionEnvelope.toOMinimal
    {A : ℝ → ℝ} (E : OMinimalExpansionEnvelope A) : OMinimal A :=
  oMinimal_of_firstOrderExpansion A E.language E.struc E.map
    E.isExpansion E.oMinimal

end AbelFormalization
