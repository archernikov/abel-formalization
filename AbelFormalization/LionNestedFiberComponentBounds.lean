import AbelFormalization.LionUpperNumbersCenterControl
import Mathlib.Topology.Separation.Regular

/-!
# Component bounds under Lion's nested-fiber limits

Lion's Lemma 6 writes an arbitrary fiber as an increasing union of decreasing
intersections of compact generic fibers.  This file records the topological
component-count facts used in that last passage.  The first theorem below is
the increasing-union half of the argument.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Nested compact intersections -/

/-- If a decreasing sequence of compact sets has intersection contained in
an open set, one member of the sequence is already contained in that open
set. -/
theorem exists_nat_subset_of_iInter_of_antitone_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : ℕ → Set X) (hanti : Antitone K)
    (hcompact : ∀ i, IsCompact (K i))
    {O : Set X} (hOopen : IsOpen O)
    (hsubset : (⋂ i, K i) ⊆ O) :
    ∃ i, K i ⊆ O := by
  classical
  by_contra hnone
  push Not at hnone
  let T : ℕ → Set X := fun i ↦ K i ∩ Oᶜ
  have hTnonempty (i : ℕ) : (T i).Nonempty := by
    obtain ⟨x, hxK, hxO⟩ := Set.not_subset.mp (hnone i)
    exact ⟨x, hxK, hxO⟩
  have hTsucc (i : ℕ) : T (i + 1) ⊆ T i := by
    intro x hx
    exact ⟨hanti (Nat.le_succ i) hx.1, hx.2⟩
  have hTzero : IsCompact (T 0) :=
    (hcompact 0).inter_right hOopen.isClosed_compl
  have hTclosed (i : ℕ) : IsClosed (T i) :=
    (hcompact i).isClosed.inter hOopen.isClosed_compl
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      T hTsucc hTnonempty hTzero hTclosed
  have hxT : ∀ i, x ∈ T i := Set.mem_iInter.mp hx
  have hxK : x ∈ ⋂ i, K i :=
    Set.mem_iInter.mpr (fun i ↦ (hxT i).1)
  exact (hxT 0).2 (hsubset hxK)

/-- The intersection of a decreasing sequence of nonempty compact connected
sets in a normal Hausdorff space is connected. -/
theorem isConnected_iInter_of_antitone_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → Set X) (hanti : Antitone K)
    (hcompact : ∀ i, IsCompact (K i))
    (hconnected : ∀ i, IsConnected (K i)) :
    IsConnected (⋂ i, K i) := by
  classical
  let C : Set X := ⋂ i, K i
  have hCclosed : IsClosed C :=
    isClosed_iInter (fun i ↦ (hcompact i).isClosed)
  have hCcompact : IsCompact C :=
    (hcompact 0).of_isClosed_subset hCclosed (Set.iInter_subset K 0)
  have hCnonempty : C.Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K (fun i ↦ hanti (Nat.le_succ i))
      (fun i ↦ (hconnected i).nonempty) (hcompact 0)
      (fun i ↦ (hcompact i).isClosed)
  refine ⟨hCnonempty, ?_⟩
  intro u v hu hv hCuv hCu hCv
  by_contra hno
  let A : Set X := C ∩ u
  let B : Set X := C ∩ v
  have hAeq : A = C ∩ vᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxv
      exact hno ⟨x, hx.1, hx.2, hxv⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hCuv hx.1 with hxu | hxv
      · exact hxu
      · exact False.elim (hx.2 hxv)
  have hBeq : B = C ∩ uᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxu
      exact hno ⟨x, hx.1, hxu, hx.2⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases hCuv hx.1 with hxu | hxv
      · exact False.elim (hx.2 hxu)
      · exact hxv
  have hAcompact : IsCompact A := by
    rw [hAeq]
    exact hCcompact.inter_right hv.isClosed_compl
  have hBcompact : IsCompact B := by
    rw [hBeq]
    exact hCcompact.inter_right hu.isClosed_compl
  have hABdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hno ⟨x, hxA.1, hxA.2, hxB.2⟩
  obtain ⟨U, V, hUopen, hVopen, hAU, hBV, hUV⟩ :=
    normal_separation hAcompact.isClosed hBcompact.isClosed hABdisj
  have hCsubset : C ⊆ U ∪ V := by
    intro x hxC
    rcases hCuv hxC with hxu | hxv
    · exact Or.inl (hAU ⟨hxC, hxu⟩)
    · exact Or.inr (hBV ⟨hxC, hxv⟩)
  obtain ⟨i, hi⟩ :=
    exists_nat_subset_of_iInter_of_antitone_isCompact
      K hanti hcompact (hUopen.union hVopen) hCsubset
  obtain ⟨x, hxC, hxu⟩ := hCu
  obtain ⟨y, hyC, hyv⟩ := hCv
  have hxKi : x ∈ K i := Set.mem_iInter.mp hxC i
  have hyKi : y ∈ K i := Set.mem_iInter.mp hyC i
  have hmeet := (hconnected i).isPreconnected U V hUopen hVopen hi
    ⟨x, hxKi, hAU ⟨hxC, hxu⟩⟩
    ⟨y, hyKi, hBV ⟨hyC, hyv⟩⟩
  obtain ⟨z, _hzKi, hzU, hzV⟩ := hmeet
  exact Set.disjoint_left.mp hUV hzU hzV

/-- A connected component inside a compact Hausdorff set, viewed in the
ambient space, is compact. -/
theorem isCompact_connectedComponentIn_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) :
    IsCompact (connectedComponentIn K x) := by
  rw [connectedComponentIn_eq_image hx]
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- A common finite bound on the connected components of a decreasing
sequence of compact sets also bounds the components of its intersection.

This is the inner-intersection step in Lion's Lemma 6. -/
theorem enatCard_connectedComponents_iInter_nat_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → Set X) (hanti : Antitone K)
    (hcompact : ∀ i, IsCompact (K i)) (N : ℕ)
    (hbound : ∀ i,
      ENat.card (ConnectedComponents (K i)) ≤ (N : ℕ∞)) :
    ENat.card (ConnectedComponents (⋂ i, K i)) ≤ (N : ℕ∞) := by
  classical
  by_contra hnot
  obtain ⟨selected, hselected⟩ :=
    exists_fin_succ_injection_of_enatCard_not_le_lion hnot
  choose point hpoint using
    fun i ↦ ConnectedComponents.surjective_coe (selected i)
  let pointAt (n : ℕ) (i : Fin (N + 1)) : K n :=
    ⟨(point i : X), Set.mem_iInter.mp (point i).property n⟩

  have hpair (i j : Fin (N + 1)) (hij : i ≠ j) :
      ∃ n,
        ConnectedComponents.mk (pointAt n i) ≠
          ConnectedComponents.mk (pointAt n j) := by
    by_contra hall
    push Not at hall
    let D : ℕ → Set X :=
      fun n ↦ connectedComponentIn (K n) (point i : X)
    have hpointK (n : ℕ) : (point i : X) ∈ K n :=
      Set.mem_iInter.mp (point i).property n
    have hDanti : Antitone D := by
      intro m n hmn
      exact connectedComponentIn_mono (point i : X) (hanti hmn)
    have hDcompact (n : ℕ) : IsCompact (D n) :=
      isCompact_connectedComponentIn_of_isCompact
        (hcompact n) (hpointK n)
    have hDconnected (n : ℕ) : IsConnected (D n) :=
      isConnected_connectedComponentIn_iff.mpr (hpointK n)
    have hDintersection : IsConnected (⋂ n, D n) :=
      isConnected_iInter_of_antitone_isCompact
        D hDanti hDcompact hDconnected
    have hiD : (point i : X) ∈ ⋂ n, D n := by
      refine Set.mem_iInter.mpr ?_
      intro n
      exact mem_connectedComponentIn (hpointK n)
    have hjD : (point j : X) ∈ ⋂ n, D n := by
      refine Set.mem_iInter.mpr ?_
      intro n
      change (point j : X) ∈
        connectedComponentIn (K n) (point i : X)
      rw [connectedComponentIn_eq_image (hpointK n)]
      refine ⟨pointAt n j, ?_, rfl⟩
      exact ConnectedComponents.coe_eq_coe'.mp (hall n).symm
    have hDsubset : (⋂ n, D n) ⊆ ⋂ n, K n := by
      intro x hx
      refine Set.mem_iInter.mpr ?_
      intro n
      exact connectedComponentIn_subset (K n) (point i : X)
        (Set.mem_iInter.mp hx n)
    have hjComponent :
        (point j : X) ∈
          connectedComponentIn (⋂ n, K n) (point i : X) :=
      (hDintersection.isPreconnected.subset_connectedComponentIn
        hiD hDsubset) hjD
    rw [connectedComponentIn_eq_image (point i).property] at hjComponent
    obtain ⟨q, hq, hqval⟩ := hjComponent
    have hqeq : q = point j := Subtype.ext hqval
    subst q
    have hcomponents :
        ConnectedComponents.mk (point i) =
          ConnectedComponents.mk (point j) :=
      (ConnectedComponents.coe_eq_coe'.mpr hq).symm
    have hselectedEq : selected i = selected j := by
      rw [← hpoint i, ← hpoint j]
      exact hcomponents
    exact hij (hselected hselectedEq)

  let pairStage : Fin (N + 1) × Fin (N + 1) → ℕ := fun ij ↦
    if h : ij.1 ≠ ij.2 then Classical.choose (hpair ij.1 ij.2 h) else 0
  have hpairStage (i j : Fin (N + 1)) (hij : i ≠ j) :
      ConnectedComponents.mk (pointAt (pairStage (i, j)) i) ≠
        ConnectedComponents.mk (pointAt (pairStage (i, j)) j) := by
    have hpick : pairStage (i, j) =
        Classical.choose (hpair i j hij) := by
      dsimp only [pairStage]
      exact dite_eq_left hij
    rw [hpick]
    exact Classical.choose_spec (hpair i j hij)
  let J : ℕ := Finset.univ.sup pairStage
  have hstage_le (i j : Fin (N + 1)) : pairStage (i, j) ≤ J := by
    exact Finset.le_sup (f := pairStage) (Finset.mem_univ (i, j))
  have hJseparates (i j : Fin (N + 1)) (hij : i ≠ j) :
      ConnectedComponents.mk (pointAt J i) ≠
        ConnectedComponents.mk (pointAt J j) := by
    intro hsame
    let n : ℕ := pairStage (i, j)
    have hKsub : K J ⊆ K n := hanti (hstage_le i j)
    let incl : K J → K n := Set.inclusion hKsub
    have hincl : Continuous incl := continuous_inclusion hKsub
    have hmapped := congrArg hincl.connectedComponentsMap hsame
    have hinclPoint (k : Fin (N + 1)) :
        incl (pointAt J k) = pointAt n k := Subtype.ext rfl
    have hsameAtN :
        ConnectedComponents.mk (pointAt n i) =
          ConnectedComponents.mk (pointAt n j) := by
      simpa only [Continuous.connectedComponentsMap_mk,
        hinclPoint] using hmapped
    exact hpairStage i j hij hsameAtN
  have hJinjective : Function.Injective
      (fun i ↦ ConnectedComponents.mk (pointAt J i)) := by
    intro i j hsame
    by_contra hij
    exact hJseparates i j hij hsame
  have hlower :
      (N + 1 : ℕ∞) ≤ ENat.card (ConnectedComponents (K J)) := by
    simpa using ENat.card_le_card_of_injective hJinjective
  have hcontra : (N + 1 : ℕ∞) ≤ (N : ℕ∞) :=
    hlower.trans (hbound J)
  have : N + 1 ≤ N := ENat.natCast_le_natCast.mp hcontra
  omega

/-- A common finite bound on the connected components of an increasing
sequence of sets also bounds the connected components of its union.

This is the outer-union step in the proof of Lion's Theorem 2. -/
theorem enatCard_connectedComponents_iUnion_nat_le
    {X : Type*} [TopologicalSpace X]
    (S : ℕ → Set X) (hmono : Monotone S) (N : ℕ)
    (hbound : ∀ j,
      ENat.card (ConnectedComponents (S j)) ≤ (N : ℕ∞)) :
    ENat.card (ConnectedComponents (⋃ j, S j)) ≤ (N : ℕ∞) := by
  by_contra hnot
  obtain ⟨selected, hselected⟩ :=
    exists_fin_succ_injection_of_enatCard_not_le_lion hnot
  choose point hpoint using
    fun i ↦ ConnectedComponents.surjective_coe (selected i)
  choose stage hstage using
    fun i ↦ Set.mem_iUnion.mp (point i).property

  let J : ℕ := Finset.univ.sup stage
  have hstage_le (i : Fin (N + 1)) : stage i ≤ J := by
    exact Finset.le_sup (f := stage) (Finset.mem_univ i)
  have hpoint_stage (i : Fin (N + 1)) :
      (point i : X) ∈ S J :=
    hmono (hstage_le i) (hstage i)
  let liftedPoint : Fin (N + 1) → S J :=
    fun i ↦ ⟨(point i : X), hpoint_stage i⟩
  let incl : S J → (⋃ j, S j) :=
    Set.inclusion (Set.subset_iUnion S J)
  have hincl : Continuous incl :=
    continuous_inclusion (Set.subset_iUnion S J)
  let componentMap :
      ConnectedComponents (S J) →
        ConnectedComponents (⋃ j, S j) :=
    hincl.connectedComponentsMap
  have hmap (i : Fin (N + 1)) :
      componentMap (ConnectedComponents.mk (liftedPoint i)) =
        selected i := by
    change hincl.connectedComponentsMap
        (ConnectedComponents.mk (liftedPoint i)) = selected i
    rw [Continuous.connectedComponentsMap_mk]
    calc
      ConnectedComponents.mk (incl (liftedPoint i)) =
          ConnectedComponents.mk (point i) := by
        apply congrArg ConnectedComponents.mk
        exact Subtype.ext rfl
      _ = selected i := hpoint i
  have hlifted : Function.Injective
      (fun i ↦ ConnectedComponents.mk (liftedPoint i)) := by
    intro i j hij
    apply hselected
    rw [← hmap i, ← hmap j]
    exact congrArg componentMap hij
  have hlower :
      (N + 1 : ℕ∞) ≤ ENat.card (ConnectedComponents (S J)) := by
    simpa using ENat.card_le_card_of_injective hlifted
  have hcontra : (N + 1 : ℕ∞) ≤ (N : ℕ∞) :=
    hlower.trans (hbound J)
  have : N + 1 ≤ N := ENat.natCast_le_natCast.mp hcontra
  omega

/-- Lion's complete nested-limit step: if the inner compact sequences are
decreasing, their intersections increase with the outer index, and all
approximating compact sets have at most `N` connected components, then the
resulting increasing union of decreasing intersections has at most `N`
connected components. -/
theorem enatCard_connectedComponents_iUnion_iInter_nat_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → ℕ → Set X)
    (hanti : ∀ j, Antitone (K j))
    (hcompact : ∀ j i, IsCompact (K j i))
    (houter : Monotone (fun j ↦ ⋂ i, K j i))
    (N : ℕ)
    (hbound : ∀ j i,
      ENat.card (ConnectedComponents (K j i)) ≤ (N : ℕ∞)) :
    ENat.card (ConnectedComponents (⋃ j, ⋂ i, K j i)) ≤
      (N : ℕ∞) := by
  apply enatCard_connectedComponents_iUnion_nat_le
    (fun j ↦ ⋂ i, K j i) houter N
  intro j
  exact enatCard_connectedComponents_iInter_nat_le
    (K j) (hanti j) (hcompact j) N (hbound j)

end AbelFormalization
