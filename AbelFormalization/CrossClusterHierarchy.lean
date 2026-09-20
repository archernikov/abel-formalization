import AbelFormalization.FilteredFiniteHierarchy

/-!
# Cross-cluster hierarchy after bounded logarithmic shifts

The within-cluster estimates are already supplied by
`FilteredFiniteHierarchy`.  This file proves the separate estimate used
between ordered clusters in `prop:separated`.

If the Abel-time gap from a smaller cluster to a larger cluster tends to
infinity, subtracting bounded natural numbers from the two times preserves
that divergence.  Consequently the inverse Abel value in the larger cluster
eventually exceeds every fixed iterate of `E` applied to the smaller value.
Two `E` iterates dominate one ordinary exponential once the input is at
least two, so the same conclusion holds for every fixed iterate of
`Real.exp`.

All core results are stated on an arbitrary filter.  They remain formally
true when the filter is bottom.  The final separated-restriction wrapper
states infinitude, and hence `NeBot`, as a separate hypothesis so the
nonvacuous application is explicit.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set Function
open scoped Topology

universe u v

variable {X : Type u}

/-! ## Elementary filter facts for time gaps -/

/-- Subtracting a bounded natural-valued shift preserves divergence of a
real-valued function to positive infinity. -/
theorem tendsto_sub_natCast_atTop_of_bounded
    {l : Filter X} {t : X → ℝ} (ht : Tendsto t l atTop)
    (shift : X → ℕ) (D : ℕ)
    (hshift : ∀ᶠ x in l, shift x ≤ D) :
    Tendsto (fun x => t x - (shift x : ℝ)) l atTop := by
  have hsub : Tendsto (fun y : ℝ => y - (D : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro C
    filter_upwards [eventually_ge_atTop (C + (D : ℝ))] with y hy
    linarith
  apply tendsto_atTop_mono' l _ (hsub.comp ht)
  filter_upwards [hshift] with x hx
  have hxcast : (shift x : ℝ) ≤ (D : ℝ) := by exact_mod_cast hx
  change t x - (D : ℝ) ≤ t x - (shift x : ℝ)
  linarith

/-- A divergent difference stays divergent when the upper time is lowered
by a bounded natural number and the lower time is lowered by an arbitrary
natural number.  Thus no bound on the lower shift is needed here. -/
theorem tendsto_shifted_time_gap_atTop_of_bounded
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (higherShift lowerShift : X → ℕ) (D : ℕ)
    (hhigherShift : ∀ᶠ x in l, higherShift x ≤ D) :
    Tendsto (fun x =>
      (higher x - (higherShift x : ℝ)) -
        (lower x - (lowerShift x : ℝ))) l atTop := by
  have hsub : Tendsto (fun y : ℝ => y - (D : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro C
    filter_upwards [eventually_ge_atTop (C + (D : ℝ))] with y hy
    linarith
  apply tendsto_atTop_mono' l _ (hsub.comp hgap)
  filter_upwards [hhigherShift] with x hx
  have hxcast : (higherShift x : ℝ) ≤ (D : ℝ) := by exact_mod_cast hx
  have hlowerShift : 0 ≤ (lowerShift x : ℝ) := Nat.cast_nonneg _
  change (higher x - lower x) - (D : ℝ) ≤
    (higher x - (higherShift x : ℝ)) -
      (lower x - (lowerShift x : ℝ))
  linarith

/-- Fixed-shift specialization used literally by the manuscript after the
balancing subsequence has made every operation list constant. -/
theorem tendsto_shifted_time_gap_atTop
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (higherShift lowerShift : ℕ) :
    Tendsto (fun x =>
      (higher x - (higherShift : ℝ)) -
        (lower x - (lowerShift : ℝ))) l atTop := by
  simpa only using tendsto_shifted_time_gap_atTop_of_bounded hgap
    (fun _ => higherShift) (fun _ => lowerShift) higherShift
      (Filter.Eventually.of_forall fun _ => le_rfl)

/-- A divergent gap remains divergent after enlarging its upper endpoint and
shrinking its lower endpoint.  This is the coordinatewise sandwich used to
pass from cluster extrema to arbitrary representatives. -/
theorem tendsto_gap_atTop_of_eventually_sandwiched
    {l : Filter X} {higherBase lowerBase higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higherBase x - lowerBase x) l atTop)
    (hhigher : ∀ᶠ x in l, higherBase x ≤ higher x)
    (hlower : ∀ᶠ x in l, lower x ≤ lowerBase x) :
    Tendsto (fun x => higher x - lower x) l atTop := by
  apply tendsto_atTop_mono' l _ hgap
  filter_upwards [hhigher, hlower] with x hxh hxl
  linarith

/-! ## Adjacent ordered gaps imply all pairwise ordered gaps -/

/-- If every adjacent gap between cluster extrema tends to infinity, then
the cluster minima are eventually monotone in the declared order. -/
theorem eventually_clusterMin_monotone_of_adjacent_gaps
    {l : Filter X} {k : ℕ}
    (clusterMin clusterMax : Fin (k + 1) → X → ℝ)
    (hwithin : ∀ᶠ x in l, ∀ i, clusterMin i x ≤ clusterMax i x)
    (hadjacent : ∀ i : Fin k, Tendsto (fun x =>
      clusterMin i.succ x - clusterMax i.castSucc x) l atTop) :
    ∀ᶠ x in l, Monotone (fun i => clusterMin i x) := by
  have hadjacentOrder : ∀ᶠ x in l, ∀ i : Fin k,
      clusterMax i.castSucc x ≤ clusterMin i.succ x := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (hadjacent i).eventually (eventually_ge_atTop 0)
    filter_upwards [hi] with x hx
    linarith
  filter_upwards [hwithin, hadjacentOrder] with x hxwithin hxadjacent
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact (hxwithin i.castSucc).trans (hxadjacent i)

/-- Hence every later cluster minimum has a divergent gap over every earlier
cluster maximum.  The manuscript assumes only adjacent gaps, so this theorem
is the finite ordered-cluster reduction needed before applying the
cross-cluster estimates below. -/
theorem tendsto_pairwise_cluster_gap_atTop_of_adjacent
    {l : Filter X} {k : ℕ}
    (clusterMin clusterMax : Fin (k + 1) → X → ℝ)
    (hwithin : ∀ᶠ x in l, ∀ i, clusterMin i x ≤ clusterMax i x)
    (hadjacent : ∀ i : Fin k, Tendsto (fun x =>
      clusterMin i.succ x - clusterMax i.castSucc x) l atTop)
    (i j : Fin (k + 1)) (hij : i < j) :
    Tendsto (fun x => clusterMin j x - clusterMax i x) l atTop := by
  let r : Fin k :=
    ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  have hrcast : r.castSucc = i := Fin.ext (by rfl)
  have hrsucc : r.succ ≤ j := by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_iff.mpr hij
  have hmono := eventually_clusterMin_monotone_of_adjacent_gaps
    clusterMin clusterMax hwithin hadjacent
  apply tendsto_atTop_mono' l _ (hadjacent r)
  filter_upwards [hmono] with x hxmono
  have hle := hxmono hrsucc
  rw [hrcast]
  linarith

/-! ## `E` and exponential iterates -/

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Adding a natural number to Abel time is exactly iterating `E` on the
inverse Abel value. -/
theorem E_iterate_inverse_add_nat (s : ℝ) (q : ℕ) :
    E^[q] (inverse A s) = inverse A (s + (q : ℝ)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', ih]
      calc
        E (inverse A (s + (q : ℝ))) =
            inverse A ((s + (q : ℝ)) + 1) := by
          symm
          simpa only [E] using hA.inverse_add_one (s + (q : ℝ))
        _ = inverse A (s + ((q + 1 : ℕ) : ℝ)) := by
          congr 1
          push_cast
          ring

/-- A divergent Abel-time gap makes the larger inverse value eventually
dominate every fixed `E` iterate of the smaller inverse value, uniformly
under bounded natural shifts of the larger time. -/
theorem eventually_E_iterate_inverse_shift_lt_of_gap
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (higherShift lowerShift : X → ℕ) (D q : ℕ)
    (hhigherShift : ∀ᶠ x in l, higherShift x ≤ D) :
    ∀ᶠ x in l,
      E^[q] (inverse A (lower x - (lowerShift x : ℝ))) <
        inverse A (higher x - (higherShift x : ℝ)) := by
  have hshifted := tendsto_shifted_time_gap_atTop_of_bounded
    hgap higherShift lowerShift D hhigherShift
  have hlarge := hshifted.eventually (eventually_gt_atTop (q : ℝ))
  filter_upwards [hlarge] with x hx
  rw [hA.E_iterate_inverse_add_nat]
  apply hA.inverse_strictMono
  linarith

/-- Fixed-shift form of
`eventually_E_iterate_inverse_shift_lt_of_gap`. -/
theorem eventually_E_iterate_inverse_sub_nat_lt_of_gap
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (higherShift lowerShift q : ℕ) :
    ∀ᶠ x in l,
      E^[q] (inverse A (lower x - (lowerShift : ℝ))) <
        inverse A (higher x - (higherShift : ℝ)) := by
  simpa only using hA.eventually_E_iterate_inverse_shift_lt_of_gap hgap
    (fun _ => higherShift) (fun _ => lowerShift) higherShift q
      (Filter.Eventually.of_forall fun _ => le_rfl)

end IsAbel

/-- Above input two, two `E` iterates dominate one ordinary exponential. -/
theorem exp_le_E_iterate_two {x : ℝ} (hx : 2 ≤ x) :
    Real.exp x ≤ E^[2] x := by
  have hEx : 2 ≤ E x := by
    dsimp only [E]
    linarith [Real.add_one_le_exp x]
  have hquad := Real.quadratic_le_exp_of_nonneg
    (x := E x) (zero_le_two.trans hEx)
  have hex : Real.exp x = E x + 1 := by simp [E]
  change Real.exp x ≤ Real.exp (E x) - 1
  rw [hex]
  nlinarith [sq_nonneg (E x - 2)]

/-- Therefore `2*k` iterates of `E` dominate `k` iterates of the ordinary
exponential, uniformly for every input at least two. -/
theorem exp_iterate_le_E_iterate_two_mul (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (Real.exp^[k]) x ≤ E^[2 * k] x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hxpos : 0 < x := zero_lt_two.trans_le hx
      have hxiterate : x ≤ E^[2 * k] x := by
        simpa only [Function.iterate_zero_apply] using
          (E_iterate_strictMono hxpos).monotone (Nat.zero_le (2 * k))
      have hlarge : 2 ≤ E^[2 * k] x := hx.trans hxiterate
      calc
        (Real.exp^[k + 1]) x = Real.exp ((Real.exp^[k]) x) := by
          rw [Function.iterate_succ_apply']
        _ ≤ Real.exp (E^[2 * k] x) := Real.exp_le_exp.mpr ih
        _ ≤ E^[2] (E^[2 * k] x) := exp_le_E_iterate_two hlarge
        _ = E^[2 * (k + 1)] x := by
          rw [← Function.iterate_add_apply]
          congr 1
          omega

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Cross-cluster domination by every fixed ordinary exponential iterate.
Both current Abel times may have bounded natural shifts.  Divergence of the
smaller cluster time is used only to make its inverse value eventually at
least two. -/
theorem eventually_exp_iterate_inverse_shift_lt_of_gap
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (hlower : Tendsto lower l atTop)
    (higherShift lowerShift : X → ℕ) (Dhigher Dlower k : ℕ)
    (hhigherShift : ∀ᶠ x in l, higherShift x ≤ Dhigher)
    (hlowerShift : ∀ᶠ x in l, lowerShift x ≤ Dlower) :
    ∀ᶠ x in l,
      (Real.exp^[k]) (inverse A (lower x - (lowerShift x : ℝ))) <
        inverse A (higher x - (higherShift x : ℝ)) := by
  have hE := hA.eventually_E_iterate_inverse_shift_lt_of_gap hgap
    higherShift lowerShift Dhigher (2 * k) hhigherShift
  have hlowerCurrent := tendsto_sub_natCast_atTop_of_bounded
    hlower lowerShift Dlower hlowerShift
  have htwo : ∀ᶠ x in l,
      2 ≤ inverse A (lower x - (lowerShift x : ℝ)) := by
    have htime := hlowerCurrent.eventually (eventually_ge_atTop (A 2))
    filter_upwards [htime] with x hx
    have hinverse := hA.inverse_strictMono.monotone hx
    simpa only [hA.inverse_apply (by norm_num : (0 : ℝ) < 2)] using hinverse
  filter_upwards [htwo, hE] with x hx hdom
  exact (exp_iterate_le_E_iterate_two_mul k hx).trans_lt hdom

/-- Fixed-shift form of the cross-cluster ordinary-exponential
domination theorem. -/
theorem eventually_exp_iterate_inverse_sub_nat_lt_of_gap
    {l : Filter X} {higher lower : X → ℝ}
    (hgap : Tendsto (fun x => higher x - lower x) l atTop)
    (hlower : Tendsto lower l atTop)
    (higherShift lowerShift k : ℕ) :
    ∀ᶠ x in l,
      (Real.exp^[k]) (inverse A (lower x - (lowerShift : ℝ))) <
        inverse A (higher x - (higherShift : ℝ)) := by
  simpa only using hA.eventually_exp_iterate_inverse_shift_lt_of_gap
    hgap hlower (fun _ => higherShift) (fun _ => lowerShift)
      higherShift lowerShift k
      (Filter.Eventually.of_forall fun _ => le_rfl)
      (Filter.Eventually.of_forall fun _ => le_rfl)

/-- Simultaneous version for all representatives in a finite family of
remaining smaller clusters. -/
theorem eventually_all_exp_iterate_inverse_shift_lt_of_gap
    {ι : Type v} [Fintype ι]
    {l : Filter X} {higher : X → ℝ} {lower : ι → X → ℝ}
    (hgap : ∀ i, Tendsto (fun x => higher x - lower i x) l atTop)
    (hlower : ∀ i, Tendsto (lower i) l atTop)
    (higherShift : X → ℕ) (lowerShift : ι → X → ℕ)
    (Dhigher : ℕ) (Dlower : ι → ℕ) (k : ℕ)
    (hhigherShift : ∀ᶠ x in l, higherShift x ≤ Dhigher)
    (hlowerShift : ∀ i, ∀ᶠ x in l, lowerShift i x ≤ Dlower i) :
    ∀ᶠ x in l, ∀ i,
      (Real.exp^[k]) (inverse A (lower i x - (lowerShift i x : ℝ))) <
        inverse A (higher x - (higherShift x : ℝ)) := by
  apply Filter.eventually_all.mpr
  intro i
  exact hA.eventually_exp_iterate_inverse_shift_lt_of_gap
    (hgap i) (hlower i) higherShift (lowerShift i)
      Dhigher (Dlower i) k hhigherShift (hlowerShift i)

/-- Restricted-filter form with nonvacuity kept explicit.  Without
`hInfinite`, the hierarchy conclusion still follows from the preceding
theorem but may be vacuous because `separatedRestriction` can be bottom. -/
theorem nonvacuous_crossCluster_expHierarchy_separatedRestriction
    {ι : Type v} [Fintype ι]
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ}
    {higher : ℕ → ℝ} {lower : ι → ℕ → ℝ}
    (hInfinite : (Λ ∩ Γ N).Infinite)
    (hgap : ∀ i, Tendsto (fun n => higher n - lower i n)
      (separatedRestriction Λ Γ N) atTop)
    (hlower : ∀ i, Tendsto (lower i)
      (separatedRestriction Λ Γ N) atTop)
    (higherShift : ℕ → ℕ) (lowerShift : ι → ℕ → ℕ)
    (Dhigher : ℕ) (Dlower : ι → ℕ)
    (hhigherShift : ∀ᶠ n in separatedRestriction Λ Γ N,
      higherShift n ≤ Dhigher)
    (hlowerShift : ∀ i, ∀ᶠ n in separatedRestriction Λ Γ N,
      lowerShift i n ≤ Dlower i) :
    (separatedRestriction Λ Γ N).NeBot ∧
      ∀ k : ℕ, ∀ᶠ n in separatedRestriction Λ Γ N, ∀ i,
        (Real.exp^[k])
            (inverse A (lower i n - (lowerShift i n : ℝ))) <
          inverse A (higher n - (higherShift n : ℝ)) := by
  refine ⟨separatedRestriction_neBot_iff.mpr hInfinite, ?_⟩
  intro k
  exact hA.eventually_all_exp_iterate_inverse_shift_lt_of_gap
    hgap hlower higherShift lowerShift Dhigher Dlower k
      hhigherShift hlowerShift

end IsAbel

end AbelFormalization
