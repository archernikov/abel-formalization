import AbelFormalization.CharbonnelSection56InfiniteFiberLocus

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

theorem test_infinite_maxwellScalarFiber_iff_encard_ge_succ_of_component_bound
    {p N : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hcomponents :
      ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N) :
    (maxwellScalarFiber R x).Infinite ↔
      (N + 1 : ℕ∞) ≤ (maxwellScalarFiber R x).encard := by
  constructor
  · intro hinfinite
    rw [hinfinite.encard_eq]
    exact le_top
  · intro hcard
    have hx : x ∈
        maxwellScalarFiberCardinalityAtLeast Set.univ R (N + 1) :=
      (mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
        Set.univ R x).mpr ⟨Set.mem_univ x, hcard⟩
    obtain ⟨_hxuniv, y, hy⟩ :=
      (mem_maxwellScalarFiberCardinalityAtLeast_succ_iff
        Set.univ R x).mp hx
    obtain ⟨a, b, hab, hIcc⟩ :=
      exists_interval_subset_maxwellScalarFiber_of_orderedWitness
        hcomponents hy
    exact (Set.Icc_infinite hab).mono hIcc

theorem test_infiniteLocus_eq_cardinalityAtLeast_succ_of_component_bound
    {n N : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hcomponents : ∀ x : RealEuclidean n,
      ENat.card (ConnectedComponents (maxwellScalarFiber S x)) ≤ N) :
    charbonnelInfiniteVerticalFiberLocus S =
      maxwellScalarFiberCardinalityAtLeast Set.univ S (N + 1) := by
  ext x
  rw [mem_charbonnelInfiniteVerticalFiberLocus_iff,
    mem_maxwellScalarFiberCardinalityAtLeast_iff_encard]
  simp only [Set.mem_univ, true_and]
  change (maxwellScalarFiber S x).Infinite ↔ _
  exact
    test_infinite_maxwellScalarFiber_iff_encard_ge_succ_of_component_bound
      (hcomponents x)

theorem test_charbonnelInfiniteVerticalFiberLocus_mem_charbonnelClosure_of_ws5
    {S0 : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S0))
    {n : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + 1))}
    (hSmem : S ∈ charbonnelClosure S0 (n + 1)) :
    charbonnelInfiniteVerticalFiberLocus S ∈ charbonnelClosure S0 n := by
  obtain ⟨N, hcomponents⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hn hSmem
  rw [test_infiniteLocus_eq_cardinalityAtLeast_succ_of_component_bound
    hcomponents]
  exact maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hn
    (hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n))
    hSmem

end AbelFormalization
