import AbelFormalization.RestrictedFixedIterateShift
import AbelFormalization.RestrictedRegularZeroReclassification
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The coordinate change for merging two representatives

The manuscript replaces a pair `(s_j, s_i)` by an unbounded representative
`u` and a bounded coordinate `xi` through

`s_j = E^[K] u`,  `s_i = E^[K+k] (u+xi)`.

The full restricted-source map below implements this in two stages.  It first
warps one retained representative and the final bounded coordinate, and then
uses `restrictedSourceReclassifyAt` to move that final bounded coordinate to
the deleted representative slot.  This factorization makes all other
coordinates transparent and isolates the nonlinear Jacobian calculation.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-! ## The scalar triangular coordinate map -/

/-- The inverse pair-coordinate formula from the manuscript, in output order
`(s_j,s_i)`. -/
def fixedIteratePairMerge (K k : ℕ) : ℝ × ℝ → ℝ × ℝ :=
  fun z ↦ (E^[K] z.1, E^[K + k] (z.1 + z.2))

/-- Every iterate of `E` has strictly positive derivative. -/
theorem deriv_E_iterate_pos (d : ℕ) (x : ℝ) : 0 < deriv (E^[d]) x := by
  rw [deriv_E_iterate]
  exact Finset.prod_pos fun i _ ↦ Real.exp_pos (E^[i] x)

/-- Exact action of the derivative of the scalar pair map.  Thus its matrix
in the standard `(u,xi)` and `(s_j,s_i)` coordinates is
`[[a,0],[b,b]]`, where `a` and `b` are the two displayed iterate
derivatives. -/
theorem fderiv_fixedIteratePairMerge_apply (K k : ℕ)
    (u xi du dxi : ℝ) :
    fderiv ℝ (fixedIteratePairMerge K k) (u, xi) (du, dxi) =
      (deriv (E^[K]) u * du,
        deriv (E^[K + k]) (u + xi) * (du + dxi)) := by
  have hfirst : HasFDerivAt (fun z : ℝ × ℝ ↦ E^[K] z.1)
      (deriv (E^[K]) u • ContinuousLinearMap.fst ℝ ℝ ℝ) (u, xi) :=
    (((contDiff_E_iterate K).differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt
      (u, xi)
      hasFDerivAt_fst
  have hsum : HasFDerivAt (fun z : ℝ × ℝ ↦ z.1 + z.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ +
        ContinuousLinearMap.snd ℝ ℝ ℝ) (u, xi) :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have hsecond : HasFDerivAt
      (fun z : ℝ × ℝ ↦ E^[K + k] (z.1 + z.2))
      (deriv (E^[K + k]) (u + xi) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ +
          ContinuousLinearMap.snd ℝ ℝ ℝ)) (u, xi) :=
    (((contDiff_E_iterate (K + k)).differentiable
      (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt (u, xi) hsum
  have hpair := hfirst.prodMk hsecond
  change HasFDerivAt (fixedIteratePairMerge K k) _ (u, xi) at hpair
  rw [hpair.fderiv]
  simp [smul_eq_mul, mul_comm]
  ring

/-- The Jacobian determinant of the pair map is the positive product stated
in the manuscript. -/
theorem fixedIteratePairMerge_jacobian_pos (K k : ℕ) (u xi : ℝ) :
    0 < deriv (E^[K]) u * deriv (E^[K + k]) (u + xi) :=
  mul_pos (deriv_E_iterate_pos K u)
    (deriv_E_iterate_pos (K + k) (u + xi))

/-- The triangular pair map is globally injective. -/
theorem fixedIteratePairMerge_injective (K k : ℕ) :
    Function.Injective (fixedIteratePairMerge K k) := by
  rintro ⟨u, xi⟩ ⟨v, zeta⟩ h
  have hfirst : E^[K] u = E^[K] v := congrArg Prod.fst h
  have hu : u = v := (E_strictMono.iterate K).injective hfirst
  have hsecond : E^[K + k] (u + xi) = E^[K + k] (v + zeta) :=
    congrArg Prod.snd h
  have hsum : u + xi = v + zeta :=
    (E_strictMono.iterate (K + k)).injective hsecond
  apply Prod.ext
  · exact hu
  · linarith

/-- The triangular pair map is smooth. -/
theorem contDiff_fixedIteratePairMerge (K k : ℕ) :
    ContDiff ℝ ∞ (fixedIteratePairMerge K k) := by
  have hfirst : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ E^[K] z.1) := by
    exact (contDiff_E_iterate K).comp contDiff_fst
  have hsum : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 + z.2) :=
    contDiff_fst.add contDiff_snd
  have hsecond : ContDiff ℝ ∞
      (fun z : ℝ × ℝ ↦ E^[K + k] (z.1 + z.2)) := by
    exact (contDiff_E_iterate (K + k)).comp hsum
  exact hfirst.prodMk hsecond

/-! ## A warp before the existing linear reclassification -/

/-- Change the retained representative `j` to `E^[K] u` and the final
bounded coordinate to `E^[K+k] (u+xi)`.  All other coordinates are fixed. -/
def restrictedPairMergeWarp {m p a : ℕ} (K k : ℕ) (j : Fin (m + 1)) :
    RestrictedSource (m + 1) (p + 1) a →
      RestrictedSource (m + 1) (p + 1) a :=
  fun x ↦
    ((Function.update x.1.1 j (E^[K] (x.1.1 j)),
      Function.update x.1.2 (Fin.last p)
        (E^[K + k] (x.1.1 j + x.1.2 (Fin.last p)))),
      x.2)

@[simp]
theorem restrictedPairMergeWarp_rep_merge {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeWarp K k j x).1.1 j = E^[K] (x.1.1 j) := by
  simp [restrictedPairMergeWarp]

@[simp]
theorem restrictedPairMergeWarp_rep_of_ne {m p a : ℕ}
    (K k : ℕ) (j r : Fin (m + 1)) (hr : r ≠ j)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeWarp K k j x).1.1 r = x.1.1 r := by
  simp [restrictedPairMergeWarp, hr]

@[simp]
theorem restrictedPairMergeWarp_box_last {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeWarp K k j x).1.2 (Fin.last p) =
      E^[K + k] (x.1.1 j + x.1.2 (Fin.last p)) := by
  simp [restrictedPairMergeWarp]

@[simp]
theorem restrictedPairMergeWarp_box_castSucc {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) (r : Fin p) :
    (restrictedPairMergeWarp K k j x).1.2 r.castSucc = x.1.2 r.castSucc := by
  simp [restrictedPairMergeWarp]

/-- The explicit logarithmic unwarp.  It is a global left inverse of the
warp; its differentiability is used only where the two displayed inputs to
the logarithmic iterates are positive. -/
def restrictedPairMergeUnwarp {m p a : ℕ} (K k : ℕ)
    (j : Fin (m + 1)) :
    RestrictedSource (m + 1) (p + 1) a →
      RestrictedSource (m + 1) (p + 1) a :=
  fun y ↦
    ((Function.update y.1.1 j (L^[K] (y.1.1 j)),
      Function.update y.1.2 (Fin.last p)
        (L^[K + k] (y.1.2 (Fin.last p)) - L^[K] (y.1.1 j))),
      y.2)

private theorem pairMerge_L_E (x : ℝ) : L (E x) = x := by
  simp [L, E]

/-- The logarithmic iterate is a left inverse to the matching `E` iterate
on all real inputs. -/
theorem pairMerge_L_iterate_E_iterate (d : ℕ) (x : ℝ) :
    L^[d] (E^[d] x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply (f := L),
        Function.iterate_succ_apply' (f := E), pairMerge_L_E, ih]

/-- Exact left-inverse identity for the full warp. -/
theorem restrictedPairMergeUnwarp_warp {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1)) :
    Function.LeftInverse
      (restrictedPairMergeUnwarp (p := p) (a := a) K k j)
      (restrictedPairMergeWarp K k j) := by
  intro x
  apply Prod.ext
  · apply Prod.ext
    · funext r
      by_cases hr : r = j
      · subst r
        simp [restrictedPairMergeUnwarp, restrictedPairMergeWarp,
          pairMerge_L_iterate_E_iterate]
      · simp [restrictedPairMergeUnwarp, restrictedPairMergeWarp,
          pairMerge_L_iterate_E_iterate]
    · funext r
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simp [restrictedPairMergeUnwarp, restrictedPairMergeWarp,
          pairMerge_L_iterate_E_iterate]
      · simp [restrictedPairMergeUnwarp, restrictedPairMergeWarp,
          pairMerge_L_iterate_E_iterate]
  · rfl

/-- In particular, the warp is globally injective. -/
theorem restrictedPairMergeWarp_injective {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1)) :
    Function.Injective
      (restrictedPairMergeWarp (p := p) (a := a) K k j) :=
  (restrictedPairMergeUnwarp_warp (p := p) (a := a) K k j).injective

/-- The full warp is smooth. -/
theorem contDiff_restrictedPairMergeWarp {m p a : ℕ}
    (K k : ℕ) (j : Fin (m + 1)) :
    ContDiff ℝ ∞
      (restrictedPairMergeWarp (p := p) (a := a) K k j) := by
  have hu : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦ x.1.1 j) := by
    fun_prop
  have hxi : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        x.1.2 (Fin.last p)) := by
    fun_prop
  have hEK : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K] (x.1.1 j)) :=
    (contDiff_E_iterate K).comp hu
  have hEKk : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K + k] (x.1.1 j + x.1.2 (Fin.last p))) :=
    (contDiff_E_iterate (K + k)).comp (hu.add hxi)
  have hs : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        Function.update x.1.1 j (E^[K] (x.1.1 j))) := by
    rw [contDiff_pi]
    intro r
    by_cases hr : r = j
    · subst r
      simpa using hEK
    · simpa [hr] using (show ContDiff ℝ ∞
          (fun x : RestrictedSource (m + 1) (p + 1) a ↦ x.1.1 r) by
        fun_prop)
  have hw : ContDiff ℝ ∞
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        Function.update x.1.2 (Fin.last p)
          (E^[K + k] (x.1.1 j + x.1.2 (Fin.last p)))) := by
    rw [contDiff_pi]
    intro r
    by_cases hr : r = Fin.last p
    · subst r
      simpa using hEKk
    · simpa [hr] using (show ContDiff ℝ ∞
          (fun x : RestrictedSource (m + 1) (p + 1) a ↦ x.1.2 r) by
        fun_prop)
  exact (hs.prodMk hw).prodMk (by fun_prop)

/-- The logarithmic unwarp is smooth at the image of every point satisfying
the two positive-inner-argument conditions used in the manuscript tail. -/
theorem contDiffAt_restrictedPairMergeUnwarp_at_warp
    {m p a : ℕ} (K k : ℕ) (j : Fin (m + 1))
    {x : RestrictedSource (m + 1) (p + 1) a}
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    ContDiffAt ℝ ∞
      (restrictedPairMergeUnwarp (p := p) (a := a) K k j)
      (restrictedPairMergeWarp K k j x) := by
  have hjpos : 0 < (restrictedPairMergeWarp K k j x).1.1 j := by
    simpa using E_iterate_pos hu K
  have hipos : 0 <
      (restrictedPairMergeWarp K k j x).1.2 (Fin.last p) := by
    simpa using E_iterate_pos huxi (K + k)
  have hjcoord : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.1 j)
      (restrictedPairMergeWarp K k j x) := by
    fun_prop
  have hicoord : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦
        y.1.2 (Fin.last p))
      (restrictedPairMergeWarp K k j x) := by
    fun_prop
  have hLj : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦
        L^[K] (y.1.1 j))
      (restrictedPairMergeWarp K k j x) :=
    ContDiffAt.comp
      (f := fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.1 j)
      (restrictedPairMergeWarp K k j x)
      (contDiffAt_L_iterate hjpos K) hjcoord
  have hLi : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦
        L^[K + k] (y.1.2 (Fin.last p)))
      (restrictedPairMergeWarp K k j x) :=
    ContDiffAt.comp
      (f := fun y : RestrictedSource (m + 1) (p + 1) a ↦
        y.1.2 (Fin.last p))
      (restrictedPairMergeWarp K k j x)
      (contDiffAt_L_iterate hipos (K + k)) hicoord
  have hs : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦
        Function.update y.1.1 j (L^[K] (y.1.1 j)))
      (restrictedPairMergeWarp K k j x) := by
    rw [contDiffAt_pi]
    intro r
    by_cases hr : r = j
    · subst r
      simpa using hLj
    · simpa [hr] using (show ContDiffAt ℝ ∞
          (fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.1 r)
          (restrictedPairMergeWarp K k j x) by
        fun_prop)
  have hw : ContDiffAt ℝ ∞
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦
        Function.update y.1.2 (Fin.last p)
          (L^[K + k] (y.1.2 (Fin.last p)) - L^[K] (y.1.1 j)))
      (restrictedPairMergeWarp K k j x) := by
    rw [contDiffAt_pi]
    intro r
    by_cases hr : r = Fin.last p
    · subst r
      simpa using hLi.sub hLj
    · simpa [hr] using (show ContDiffAt ℝ ∞
          (fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.2 r)
          (restrictedPairMergeWarp K k j x) by
        fun_prop)
  exact (hs.prodMk hw).prodMk (by fun_prop)

/-- The derivative of the nonlinear warp is a linear isomorphism at every
point of the positive pair tail.  This is the coordinate-free Jacobian
invertibility statement. -/
theorem bijective_fderiv_restrictedPairMergeWarp
    {m p a : ℕ} (K k : ℕ) (j : Fin (m + 1))
    {x : RestrictedSource (m + 1) (p + 1) a}
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    Function.Bijective
      (fderiv ℝ (restrictedPairMergeWarp K k j) x) := by
  let W := restrictedPairMergeWarp (p := p) (a := a) K k j
  let U := restrictedPairMergeUnwarp (p := p) (a := a) K k j
  have hW : DifferentiableAt ℝ W x :=
    ((contDiff_restrictedPairMergeWarp (p := p) (a := a) K k j).differentiable
      (by simp)).differentiableAt
  have hU : DifferentiableAt ℝ U (W x) :=
    (contDiffAt_restrictedPairMergeUnwarp_at_warp
      (p := p) (a := a) K k j hu huxi).differentiableAt (by simp)
  have hchain := fderiv_comp (x := x) hU hW
  have hfun : U ∘ W = id := by
    funext y
    exact restrictedPairMergeUnwarp_warp (p := p) (a := a) K k j y
  have hlinear :
      (fderiv ℝ U (W x)).comp (fderiv ℝ W x) =
        ContinuousLinearMap.id ℝ
          (RestrictedSource (m + 1) (p + 1) a) := by
    calc
      (fderiv ℝ U (W x)).comp (fderiv ℝ W x) =
          fderiv ℝ (U ∘ W) x := hchain.symm
      _ = fderiv ℝ id x := by rw [hfun]
      _ = ContinuousLinearMap.id ℝ _ := fderiv_id
  have hleft : Function.LeftInverse (fderiv ℝ U (W x))
      (fderiv ℝ W x) := by
    intro v
    have hv := congrArg
      (fun D : RestrictedSource (m + 1) (p + 1) a →L[ℝ]
        RestrictedSource (m + 1) (p + 1) a ↦ D v) hlinear
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hv
  have hinj : Function.Injective (fderiv ℝ W x) := hleft.injective
  have hsurj : Function.Surjective (fderiv ℝ W x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := RestrictedSource (m + 1) (p + 1) a)
      (V₂ := RestrictedSource (m + 1) (p + 1) a) rfl).mp hinj
  exact ⟨hinj, hsurj⟩

/-! ## The full restricted-source pair merge -/

/-- Delete old representative slot `i`; retained slot `j` supplies `u`, and
the final bounded coordinate supplies `xi`. -/
def restrictedPairMergeSourceMap {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    RestrictedSource (m + 1) (p + 1) a →
      RestrictedSource ((m + 1) + 1) p a :=
  restrictedSourceReclassifyAt i ∘ restrictedPairMergeWarp K k j

@[simp]
theorem restrictedPairMergeSourceMap_pivot {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeSourceMap K k i j x).1.1 i =
      E^[K + k] (x.1.1 j + x.1.2 (Fin.last p)) := by
  simp [restrictedPairMergeSourceMap]

@[simp]
theorem restrictedPairMergeSourceMap_partner {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeSourceMap K k i j x).1.1 (i.succAbove j) =
      E^[K] (x.1.1 j) := by
  simp [restrictedPairMergeSourceMap]

@[simp]
theorem restrictedPairMergeSourceMap_other {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j r : Fin (m + 1))
    (hr : r ≠ j) (x : RestrictedSource (m + 1) (p + 1) a) :
    (restrictedPairMergeSourceMap K k i j x).1.1 (i.succAbove r) =
      x.1.1 r := by
  simp [restrictedPairMergeSourceMap, hr]

@[simp]
theorem restrictedPairMergeSourceMap_box {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) (r : Fin p) :
    (restrictedPairMergeSourceMap K k i j x).1.2 r = x.1.2 r.castSucc := by
  simp [restrictedPairMergeSourceMap]

@[simp]
theorem restrictedPairMergeSourceMap_aux {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) (r : Fin a) :
    (restrictedPairMergeSourceMap K k i j x).2 r = x.2 r := by
  rfl

theorem restrictedPairMergeSourceMap_injective {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    Function.Injective
      (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) :=
  (restrictedSourceReclassifyAt i).injective.comp
    (restrictedPairMergeWarp_injective (p := p) (a := a) K k j)

theorem contDiff_restrictedPairMergeSourceMap {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    ContDiff ℝ ∞
      (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) :=
  (restrictedSourceReclassifyAt i).contDiff.comp
    (contDiff_restrictedPairMergeWarp (p := p) (a := a) K k j)

theorem fderiv_restrictedPairMergeSourceMap {m p a : ℕ}
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a) :
    fderiv ℝ (restrictedPairMergeSourceMap K k i j) x =
      (restrictedSourceReclassifyAt (m := m + 1) (p := p) (a := a) i :
        RestrictedSource (m + 1) (p + 1) a →L[ℝ]
          RestrictedSource ((m + 1) + 1) p a).comp
        (fderiv ℝ (restrictedPairMergeWarp K k j) x) := by
  exact (restrictedSourceReclassifyAt
    (m := m + 1) (p := p) (a := a) i).comp_fderiv

/-- Coordinate-free invertibility of the full Jacobian. -/
theorem bijective_fderiv_restrictedPairMergeSourceMap
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    {x : RestrictedSource (m + 1) (p + 1) a}
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    Function.Bijective
      (fderiv ℝ (restrictedPairMergeSourceMap K k i j) x) := by
  rw [fderiv_restrictedPairMergeSourceMap]
  exact (restrictedSourceReclassifyAt i).bijective.comp
    (bijective_fderiv_restrictedPairMergeWarp
      (p := p) (a := a) K k j hu huxi)

/-- Package the invertible Jacobian as a continuous linear equivalence. -/
noncomputable def restrictedPairMergeFDerivEquiv
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    RestrictedSource (m + 1) (p + 1) a ≃L[ℝ]
      RestrictedSource ((m + 1) + 1) p a := by
  let D := fderiv ℝ (restrictedPairMergeSourceMap K k i j) x
  exact ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr
      (bijective_fderiv_restrictedPairMergeSourceMap K k i j hu huxi).1)
    (LinearMap.range_eq_top.mpr
      (bijective_fderiv_restrictedPairMergeSourceMap K k i j hu huxi).2)

/-- The packaged continuous linear equivalence has exactly the Fréchet
derivative of the source change as its underlying map. -/
theorem coe_restrictedPairMergeFDerivEquiv
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    (restrictedPairMergeFDerivEquiv K k i j x hu huxi :
      RestrictedSource (m + 1) (p + 1) a →L[ℝ]
        RestrictedSource ((m + 1) + 1) p a) =
      fderiv ℝ (restrictedPairMergeSourceMap K k i j) x := by
  rfl

/-- The full pair merge has the packaged invertible derivative. -/
theorem hasFDerivAt_restrictedPairMergeSourceMap
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p)) :
    HasFDerivAt (restrictedPairMergeSourceMap K k i j)
      (restrictedPairMergeFDerivEquiv K k i j x hu huxi :
        RestrictedSource (m + 1) (p + 1) a →L[ℝ]
          RestrictedSource ((m + 1) + 1) p a) x := by
  rw [coe_restrictedPairMergeFDerivEquiv]
  exact (((contDiff_restrictedPairMergeSourceMap
    (p := p) (a := a) K k i j).differentiable
      (by simp)).differentiableAt).hasFDerivAt

/-! ## Regular-zero transport -/

/-- Pointwise regular-zero invariance under a differentiable source map with
surjective derivative and a continuous-linear target equivalence. -/
theorem mem_regularZeroSet_comp_equiv_of_surjective_fderiv
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {phi : E' → E} (q : F ≃L[ℝ] F')
    (Omega : Set E) (f : E → F) (x : E')
    (hphi : DifferentiableAt ℝ phi x)
    (hf : DifferentiableAt ℝ f (phi x))
    (hDphi : Function.Surjective (fderiv ℝ phi x)) :
    x ∈ regularZeroSet (phi ⁻¹' Omega) (q ∘ f ∘ phi) ↔
      phi x ∈ regularZeroSet Omega f := by
  have hderiv :
      fderiv ℝ (q ∘ f ∘ phi) x =
        (q : F →L[ℝ] F').comp
          ((fderiv ℝ f (phi x)).comp (fderiv ℝ phi x)) := by
    rw [q.comp_fderiv, fderiv_comp (x := x) hf hphi]
  have hsurj :
      Function.Surjective (fderiv ℝ (q ∘ f ∘ phi) x) ↔
        Function.Surjective (fderiv ℝ f (phi x)) := by
    rw [hderiv]
    constructor
    · intro h y
      obtain ⟨z, hz⟩ := h (q y)
      refine ⟨fderiv ℝ phi x z, q.injective ?_⟩
      simpa [ContinuousLinearMap.comp_apply] using hz
    · intro h y'
      obtain ⟨y, hy⟩ := q.surjective y'
      obtain ⟨v, hv⟩ := h y
      obtain ⟨z, hz⟩ := hDphi v
      refine ⟨z, ?_⟩
      simpa [ContinuousLinearMap.comp_apply, hz, hv] using hy
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hx, hzero, hreg⟩
    refine ⟨hx, ?_, hsurj.mp hreg⟩
    apply q.injective
    simpa only [Function.comp_apply, map_zero] using hzero
  · rintro ⟨hx, hzero, hreg⟩
    refine ⟨hx, ?_, hsurj.mpr hreg⟩
    simp only [Function.comp_apply, hzero, map_zero]

/-- Reindex the old square equations and precompose them with the pair merge. -/
def restrictedPairMergedEquationFamily
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ) :
    Fin ((((m + 1) + (p + 1)) + a)) →
      RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun r x ↦
    F ((restrictedReclassificationEquationIndexEquiv (m + 1) p a).symm r)
      (restrictedPairMergeSourceMap K k i j x)

theorem constraintMap_restrictedPairMergedEquationFamily
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ) :
    constraintMap (restrictedPairMergedEquationFamily K k i j F) =
      restrictedReclassificationTargetEquiv (m + 1) p a ∘
        constraintMap F ∘ restrictedPairMergeSourceMap K k i j := by
  funext x r
  rfl

/-- Pointwise regular-zero preservation for the merged square family. -/
theorem mem_regularZeroSet_restrictedPairMergedEquationFamily_iff
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (Omega : Set (RestrictedSource ((m + 1) + 1) p a))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hu : 0 < x.1.1 j)
    (huxi : 0 < x.1.1 j + x.1.2 (Fin.last p))
    (hF : DifferentiableAt ℝ (constraintMap F)
      (restrictedPairMergeSourceMap K k i j x)) :
    x ∈ regularZeroSet
        (restrictedPairMergeSourceMap K k i j ⁻¹' Omega)
        (constraintMap (restrictedPairMergedEquationFamily K k i j F)) ↔
      restrictedPairMergeSourceMap K k i j x ∈
        regularZeroSet Omega (constraintMap F) := by
  rw [constraintMap_restrictedPairMergedEquationFamily]
  exact mem_regularZeroSet_comp_equiv_of_surjective_fderiv
    (restrictedReclassificationTargetEquiv (m + 1) p a)
    Omega (constraintMap F) x
    (((contDiff_restrictedPairMergeSourceMap
      (p := p) (a := a) K k i j).differentiable
        (by simp)).differentiableAt)
    hF
    (bijective_fderiv_restrictedPairMergeSourceMap K k i j hu huxi).2

/-- The natural open tail on which the inverse logarithmic coordinates and
the Jacobian argument above are valid. -/
def restrictedPairMergeTail {m p a : ℕ} (j : Fin (m + 1)) :
    Set (RestrictedSource (m + 1) (p + 1) a) :=
  {x | 0 < x.1.1 j ∧ 0 < x.1.1 j + x.1.2 (Fin.last p)}

/-- Set-level form of regular-zero preservation on the positive pair tail. -/
theorem regularZeroSet_restrictedPairMergedEquationFamily_tail
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (Omega : Set (RestrictedSource ((m + 1) + 1) p a))
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hF : ∀ x ∈ restrictedPairMergeTail (p := p) (a := a) j,
      DifferentiableAt ℝ (constraintMap F)
        (restrictedPairMergeSourceMap K k i j x)) :
    regularZeroSet
        (restrictedPairMergeTail j ∩
          restrictedPairMergeSourceMap K k i j ⁻¹' Omega)
        (constraintMap (restrictedPairMergedEquationFamily K k i j F)) =
      restrictedPairMergeTail j ∩
        restrictedPairMergeSourceMap K k i j ⁻¹'
          regularZeroSet Omega (constraintMap F) := by
  ext x
  constructor
  · rintro ⟨⟨htail, hOmega⟩, hzero, hreg⟩
    have hbase : x ∈ regularZeroSet
        (restrictedPairMergeSourceMap K k i j ⁻¹' Omega)
        (constraintMap (restrictedPairMergedEquationFamily K k i j F)) :=
      ⟨hOmega, hzero, hreg⟩
    have hold :=
      (mem_regularZeroSet_restrictedPairMergedEquationFamily_iff
        K k i j Omega F x htail.1 htail.2 (hF x htail)).mp hbase
    exact ⟨htail, hold⟩
  · rintro ⟨htail, hold⟩
    have hbase :=
      (mem_regularZeroSet_restrictedPairMergedEquationFamily_iff
        K k i j Omega F x htail.1 htail.2 (hF x htail)).mpr hold
    exact ⟨⟨htail, hbase.1⟩, hbase.2.1, hbase.2.2⟩

end AbelFormalization
