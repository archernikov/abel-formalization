import AbelFormalization.CharbonnelWeakStructure
import AbelFormalization.CharbonnelSection5ElementaryInputs
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Compact components remain weak-family members

The weak-selection argument first localizes a compact relation to one of its
connected components.  This file proves that this localization costs no
family closure operation.  A compact set with finitely many connected
components has clopen components.  Two complementary compact pieces can be
separated by a finite union of open sup-norm balls, and those balls are
polynomial-sign constructible in `RealEuclidean d`.

Only WS1 and WS2 are used.  No complement closure or selection theorem is
assumed.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Semialgebraic open balls and finite unions -/

/-- Finite unions indexed by a finite ordinal preserve polynomial-sign
constructibility. -/
theorem polynomialSignConstructible_iUnion_fin
    {d k : ℕ} (s : Fin k → Set (RealEuclidean d))
    (hs : ∀ i, PolynomialSignConstructible d (s i)) :
    PolynomialSignConstructible d (⋃ i, s i) := by
  induction k with
  | zero =>
      simpa using polynomialSignConstructible_empty d
  | succ k ih =>
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
      exact .union (hs 0)
        (by simpa [Function.comp_def] using
          ih (fun j ↦ s j.succ) (fun j ↦ hs j.succ))

/-- The lower coordinate inequality cutting out an open sup-norm ball. -/
def maxwellBallLowerPolynomial {d : ℕ}
    (c : RealEuclidean d) (r : ℝ) (i : Fin d) :
    MvPolynomial (Fin d) ℝ :=
  MvPolynomial.X i - MvPolynomial.C (c i - r)

/-- The upper coordinate inequality cutting out an open sup-norm ball. -/
def maxwellBallUpperPolynomial {d : ℕ}
    (c : RealEuclidean d) (r : ℝ) (i : Fin d) :
    MvPolynomial (Fin d) ℝ :=
  MvPolynomial.C (c i + r) - MvPolynomial.X i

@[simp]
theorem maxwellBallLowerPolynomial_eval
    {d : ℕ} (c : RealEuclidean d) (r : ℝ) (i : Fin d)
    (x : RealEuclidean d) :
    MvPolynomial.eval x (maxwellBallLowerPolynomial c r i) =
      x i - (c i - r) := by
  simp [maxwellBallLowerPolynomial]

@[simp]
theorem maxwellBallUpperPolynomial_eval
    {d : ℕ} (c : RealEuclidean d) (r : ℝ) (i : Fin d)
    (x : RealEuclidean d) :
    MvPolynomial.eval x (maxwellBallUpperPolynomial c r i) =
      c i + r - x i := by
  simp [maxwellBallUpperPolynomial]

/-- Every positive-radius open ball in the sup norm on `RealEuclidean d` is
polynomial-sign constructible. -/
theorem polynomialSignConstructible_ball
    {d : ℕ} (c : RealEuclidean d) {r : ℝ} (hr : 0 < r) :
    PolynomialSignConstructible d (Metric.ball c r) := by
  have hconstraints : PolynomialSignConstructible d
      (⋂ i : Fin d,
        {x : RealEuclidean d |
          0 < MvPolynomial.eval x (maxwellBallLowerPolynomial c r i)} ∩
        {x : RealEuclidean d |
          0 < MvPolynomial.eval x (maxwellBallUpperPolynomial c r i)}) :=
    polynomialSignConstructible_iInter_fin _ fun i ↦
      .inter (.pos (maxwellBallLowerPolynomial c r i))
        (.pos (maxwellBallUpperPolynomial c r i))
  convert hconstraints using 1
  rw [ball_pi c hr]
  ext x
  simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq, mem_pi, mem_univ,
    true_implies, Metric.mem_ball, Real.dist_eq,
    maxwellBallLowerPolynomial_eval, maxwellBallUpperPolynomial_eval]
  constructor
  · intro hx i
    have hi := hx i
    rw [abs_lt] at hi
    constructor <;> linarith
  · intro hx i
    have hi := hx i
    rw [abs_lt]
    constructor <;> linarith [hi.1, hi.2]

/-- Every point of a positive-dimensional Euclidean coordinate space is a
polynomial-sign constructible singleton. -/
theorem polynomialSignConstructible_singleton
    {d : ℕ} (c : RealEuclidean d) :
    PolynomialSignConstructible d ({c} : Set (RealEuclidean d)) := by
  have hconstraints : PolynomialSignConstructible d
      (⋂ i : Fin d,
        {x : RealEuclidean d |
          MvPolynomial.eval x
            (MvPolynomial.X i - MvPolynomial.C (c i)) = 0}) :=
    polynomialSignConstructible_iInter_fin _ fun i ↦
      .zero (MvPolynomial.X i - MvPolynomial.C (c i))
  convert hconstraints using 1
  ext x
  simp only [mem_singleton_iff, mem_iInter, mem_ofPred_eq]
  constructor
  · intro h
    subst x
    intro i
    simp
  · intro h
    funext i
    have hi : x i - c i = 0 := by simpa using h i
    linarith

/-- A union of balls whose centers form a finite set is polynomial-sign
constructible. -/
theorem polynomialSignConstructible_biUnion_balls_of_finite
    {d : ℕ} {t : Set (RealEuclidean d)} (ht : t.Finite)
    {r : ℝ} (hr : 0 < r) :
    PolynomialSignConstructible d (⋃ x ∈ t, Metric.ball x r) := by
  classical
  induction t, ht using Set.Finite.induction_on with
  | empty =>
      simpa using polynomialSignConstructible_empty d
  | @insert a t hat ht ih =>
      rw [show (⋃ x ∈ insert a t, Metric.ball x r) =
          Metric.ball a r ∪ ⋃ x ∈ t, Metric.ball x r by simp]
      exact .union (polynomialSignConstructible_ball a hr) ih

/-! ## Isolating compact connected components -/

/-- The ambient carrier of one connected component of a subset. -/
def maxwellConnectedComponentCarrier
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) : Set E :=
  Subtype.val ''
    ((ConnectedComponents.mk : A → ConnectedComponents A) ⁻¹' {c})

/-- The complementary union of all other components, viewed in the ambient
space. -/
def maxwellOtherComponentsCarrier
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) : Set E :=
  Subtype.val ''
    (((ConnectedComponents.mk : A → ConnectedComponents A) ⁻¹' {c})ᶜ)

theorem maxwell_connectedComponentCarrier_subset
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) :
    maxwellConnectedComponentCarrier c ⊆ A := by
  rintro x ⟨p, _hp, rfl⟩
  exact p.property

theorem maxwell_otherComponentsCarrier_subset
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) :
    maxwellOtherComponentsCarrier c ⊆ A := by
  rintro x ⟨p, _hp, rfl⟩
  exact p.property

/-- The ambient carrier really is a connected set, independently of the
later compactness and finiteness hypotheses. -/
theorem maxwell_connectedComponentCarrier_isConnected
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) :
    IsConnected (maxwellConnectedComponentCarrier c) := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe c
  have hcarrier : maxwellConnectedComponentCarrier c =
      Subtype.val '' connectedComponent p := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      exact ConnectedComponents.coe_eq_coe'.mp (hq.trans hp.symm)
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      exact (ConnectedComponents.coe_eq_coe'.mpr hq).trans hp
  rw [hcarrier]
  exact isConnected_connectedComponent.image Subtype.val
    continuous_subtype_val.continuousOn

/-- Every connected-component carrier of a compact Hausdorff set is compact.
Unlike the later component-isolator theorem, this does not require the set to
have only finitely many connected components. -/
theorem maxwell_connectedComponentCarrier_isCompact_of_isCompact
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hAcompact : IsCompact A)
    (c : ConnectedComponents A) :
    IsCompact (maxwellConnectedComponentCarrier c) := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe c
  have hcarrier : maxwellConnectedComponentCarrier c =
      Subtype.val '' connectedComponent p := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      exact ConnectedComponents.coe_eq_coe'.mp (hq.trans hp.symm)
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      exact (ConnectedComponents.coe_eq_coe'.mpr hq).trans hp
  rw [hcarrier]
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

theorem maxwell_componentCarrier_union_other
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) :
    maxwellConnectedComponentCarrier c ∪
        maxwellOtherComponentsCarrier c = A := by
  ext x
  simp only [maxwellConnectedComponentCarrier,
    maxwellOtherComponentsCarrier, mem_union, mem_image, mem_preimage,
    mem_singleton_iff, mem_compl_iff, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor
  · rintro (⟨hxA, _⟩ | ⟨hxA, _⟩) <;> exact hxA
  · intro hxA
    by_cases hxc : ConnectedComponents.mk ⟨x, hxA⟩ = c
    · exact Or.inl ⟨hxA, hxc⟩
    · exact Or.inr ⟨hxA, hxc⟩

theorem maxwell_componentCarrier_disjoint_other
    {E : Type*} [TopologicalSpace E] {A : Set E}
    (c : ConnectedComponents A) :
    Disjoint (maxwellConnectedComponentCarrier c)
      (maxwellOtherComponentsCarrier c) := by
  rw [Set.disjoint_left]
  intro x hxP hxQ
  rcases hxP with ⟨p, hp, rfl⟩
  rcases hxQ with ⟨q, hq, hqp⟩
  have hpq : p = q := Subtype.ext hqp.symm
  subst q
  exact hq hp

/-- In a compact Hausdorff set with finitely many connected components, one
component and the union of all the other components are compact ambient
subsets. -/
theorem maxwell_componentCarriers_isCompact
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hAcompact : IsCompact A)
    (hfinite : Finite (ConnectedComponents A))
    (c : ConnectedComponents A) :
    IsCompact (maxwellConnectedComponentCarrier c) ∧
      IsCompact (maxwellOtherComponentsCarrier c) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
  letI : Finite (ConnectedComponents A) := hfinite
  let T : Set A :=
    (ConnectedComponents.mk : A → ConnectedComponents A) ⁻¹' {c}
  have hTclopen : IsClopen T :=
    (isClopen_discrete ({c} : Set (ConnectedComponents A))).preimage
      ConnectedComponents.continuous_coe
  constructor
  · exact hTclopen.1.isCompact.image continuous_subtype_val
  · exact hTclopen.compl.1.isCompact.image continuous_subtype_val

/-- A compact connected component can be cut out of the ambient compact set
by a polynomial-sign constructible neighborhood. -/
theorem exists_polynomialSignConstructible_component_isolator
    {d : ℕ} {A : Set (RealEuclidean d)} (hAcompact : IsCompact A)
    (hfinite : Finite (ConnectedComponents A))
    (c : ConnectedComponents A) :
    ∃ O : Set (RealEuclidean d),
      PolynomialSignConstructible d O ∧
        A ∩ O = maxwellConnectedComponentCarrier c := by
  classical
  let P : Set (RealEuclidean d) := maxwellConnectedComponentCarrier c
  let Q : Set (RealEuclidean d) := maxwellOtherComponentsCarrier c
  have hcompact := maxwell_componentCarriers_isCompact hAcompact hfinite c
  have hPcompact : IsCompact P := hcompact.1
  have hQcompact : IsCompact Q := hcompact.2
  have hPnonempty : P.Nonempty := by
    obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe c
    exact ⟨p, ⟨p, hp, rfl⟩⟩
  have hPdisjQ : Disjoint P Q :=
    maxwell_componentCarrier_disjoint_other c
  by_cases hQempty : Q = ∅
  · refine ⟨Set.univ, polynomialSignConstructible_univ d, ?_⟩
    rw [inter_univ]
    have hpartition := maxwell_componentCarrier_union_other c
    simpa only [P, Q, hQempty, union_empty] using hpartition.symm
  · have hQnonempty : Q.Nonempty := Set.nonempty_iff_ne_empty.mpr hQempty
    have hQclosed : IsClosed Q := hQcompact.isClosed
    obtain ⟨p0, hp0P, hp0min⟩ :=
      hPcompact.exists_isMinOn hPnonempty
        (Metric.continuous_infDist_pt Q).continuousOn
    let delta : ℝ := Metric.infDist p0 Q
    have hp0notQ : p0 ∉ Q :=
      Set.disjoint_left.mp hPdisjQ hp0P
    have hdelta : 0 < delta := by
      exact (hQclosed.notMem_iff_infDist_pos hQnonempty).mp hp0notQ
    have hmin : ∀ p ∈ P, delta ≤ Metric.infDist p Q := by
      intro p hp
      exact hp0min hp
    obtain ⟨t, htP, htfinite, hPcover⟩ :=
      hPcompact.finite_cover_balls (half_pos hdelta)
    let O : Set (RealEuclidean d) :=
      ⋃ p ∈ t, Metric.ball p (delta / 2)
    have hOconstructible : PolynomialSignConstructible d O := by
      exact polynomialSignConstructible_biUnion_balls_of_finite
        htfinite (half_pos hdelta)
    have hOdisjQ : Disjoint O Q := by
      rw [Set.disjoint_left]
      intro x hxO hxQ
      obtain ⟨p, hpT, hxp⟩ := Set.mem_iUnion₂.mp hxO
      have hpP : p ∈ P := htP hpT
      have hinf : Metric.infDist p Q ≤ dist p x :=
        Metric.infDist_le_dist_of_mem hxQ
      have hdist : dist p x < delta / 2 := by
        simpa only [Metric.mem_ball, dist_comm] using hxp
      have hhalf : delta / 2 < delta := by linarith
      exact (not_lt_of_ge ((hmin p hpP).trans hinf)) (hdist.trans hhalf)
    refine ⟨O, hOconstructible, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      have hxpart : x ∈ P ∪ Q := by
        rw [maxwell_componentCarrier_union_other c]
        exact hx.1
      rcases hxpart with hxP | hxQ
      · exact hxP
      · exact False.elim (Set.disjoint_left.mp hOdisjQ hx.2 hxQ)
    · intro x hxP
      constructor
      · rw [← maxwell_componentCarrier_union_other c]
        exact Or.inl hxP
      · exact hPcover hxP

/-- Every connected component of a compact weak-family member is again a
member of that family. -/
theorem compact_connectedComponentCarrier_mem
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {d : ℕ} (hd : 0 < d) {A : Set (RealEuclidean d)}
    (hAcompact : IsCompact A) (hAmem : A ∈ C d)
    (hfinite : Finite (ConnectedComponents A))
    (c : ConnectedComponents A) :
    maxwellConnectedComponentCarrier c ∈ C d := by
  obtain ⟨O, hOconstructible, hAO⟩ :=
    exists_polynomialSignConstructible_component_isolator
      hAcompact hfinite c
  rw [← hAO]
  exact hC.ws1_inter hd hAmem
    (hC.ws2_polynomialSign hd hOconstructible)

/-- WS5 supplies the finiteness input, so compact components of members of an
o-minimal weak structure remain members automatically. -/
theorem PositiveArityOMinimalWeakSetStructure.compact_connectedComponentCarrier_mem
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {d : ℕ} (hd : 0 < d) {A : Set (RealEuclidean d)}
    (hAcompact : IsCompact A) (hAmem : A ∈ C d)
    (c : ConnectedComponents A) :
    maxwellConnectedComponentCarrier c ∈ C d := by
  obtain ⟨N, hN⟩ := hC.ws5_affineSections hd hAmem
  have hcard := hN (⊤ : AffineSubspace ℝ (RealEuclidean d))
  rw [AffineSubspace.top_coe, inter_univ] at hcard
  have hfinite : Finite (ConnectedComponents A) := by
    rw [← ENat.card_lt_top]
    exact hcard.trans_lt (WithTop.coe_lt_top N)
  exact AbelFormalization.compact_connectedComponentCarrier_mem
    hC.toPositiveArityWeakSetStructure
    hd hAcompact hAmem hfinite c

end AbelFormalization
