import AbelFormalization.IdealHeight
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Height under specialization of a saturated one-parameter ideal

This is the height step needed after identifying a full weighted initial
ideal with the zero-parameter specialization of its Laurent contraction.
The saturation hypothesis is actual cancellation of multiplication by the
parameter in ideal membership. It does not assume a height conclusion.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R]

/-- An element cancellable modulo an ideal avoids each minimal prime over it. -/
theorem ideal_notMem_minimalPrimes_of_cancel (J : Ideal R) (x : R)
    (hcancel : ∀ f, x * f ∈ J → f ∈ J) {q : Ideal R}
    (hq : q ∈ J.minimalPrimes) : x ∉ q := by
  intro hx
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hq hx
  exact hy (hcancel y hxy)

/-- Specializing a parameter-saturated ideal at zero cannot decrease height.
A one-variable polynomial ring is written using `Unit` as its index type. -/
theorem mvPolynomial_height_le_eval_zero_of_saturated [IsNoetherianRing R]
    (J : Ideal (MvPolynomial Unit R))
    (hsat : ∀ f, MvPolynomial.X () * f ∈ J → f ∈ J) :
    J.height ≤ (J.map (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Unit => 0))).height := by
  let ev : MvPolynomial Unit R →+* R :=
    MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Unit => 0)
  change J.height ≤ (J.map ev).height
  rw [(J.map ev).height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun p hp => ?_
  have : p.IsPrime := hp.isPrime
  let P : Ideal (MvPolynomial Unit R) := p.comap ev
  have : P.IsPrime := inferInstance
  have hJP : J ≤ P := Ideal.map_le_iff_le_comap.mp hp.le
  have hXP : MvPolynomial.X () ∈ P := by
    change ev (MvPolynomial.X ()) ∈ p
    simp [ev]
  have hPC : P.comap MvPolynomial.C = p := by
    ext x
    change ev (MvPolynomial.C x) ∈ p ↔ x ∈ p
    simp [ev]
  obtain ⟨q, hq, hqP⟩ := Ideal.exists_minimalPrimes_le hJP
  have : q.IsPrime := hq.isPrime
  have hqX : MvPolynomial.X () ∉ q :=
    ideal_notMem_minimalPrimes_of_cancel J _ hsat hq
  have hlt : q < P := lt_of_le_of_ne hqP (by
    intro he
    exact hqX (he.symm ▸ hXP))
  apply (ENat.add_le_add_iff_right (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
  calc
    J.height + 1 ≤ q.height + 1 := add_le_add (Ideal.height_mono hq.le) le_rfl
    _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    _ ≤ p.height + 1 := by
      simpa [hPC] using mvPolynomial_prime_height_le_comap_add_card P

/-- The one-variable polynomial form: cancellation by `X` modulo an ideal
implies that evaluation at zero cannot decrease its height. -/
theorem polynomial_height_le_eval_zero_of_saturated [IsNoetherianRing R]
    (J : Ideal (Polynomial R))
    (hsat : ∀ f, Polynomial.X * f ∈ J → f ∈ J) :
    J.height ≤ (J.map (Polynomial.evalRingHom (0 : R))).height := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  let K : Ideal (MvPolynomial Unit R) := J.comap e.toRingHom
  let ev : MvPolynomial Unit R →+* R :=
    MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Unit => 0)
  have hX : e (MvPolynomial.X ()) = Polynomial.X := by
    change MvPolynomial.eval₂ Polynomial.C (fun _ : Unit => Polynomial.X)
      (MvPolynomial.X ()) = Polynomial.X
    exact MvPolynomial.eval₂_X _ _ _
  have hKsat : ∀ f, MvPolynomial.X () * f ∈ K → f ∈ K := by
    intro f hf
    change e f ∈ J
    apply hsat
    change e (MvPolynomial.X () * f) ∈ J at hf
    simpa only [map_mul, hX] using hf
  have hcomp : (Polynomial.evalRingHom (0 : R)).comp e.toRingHom = ev := by
    apply RingHom.ext
    intro f
    change Polynomial.eval₂ (RingHom.id R) 0 ((MvPolynomial.uniqueAlgEquiv R Unit) f) =
      MvPolynomial.eval₂ (RingHom.id R) (fun _ : Unit => 0) f
    exact MvPolynomial.eval₂_const_uniqueAlgEquiv
  have hmap : K.map ev = J.map (Polynomial.evalRingHom (0 : R)) := by
    rw [← hcomp, ← Ideal.map_map]
    rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective J]
  have hheight : K.height = J.height := e.toRingEquiv.height_comap J
  have h := mvPolynomial_height_le_eval_zero_of_saturated K hKsat
  change K.height ≤ (K.map ev).height at h
  simpa only [hmap, hheight] using h

end AbelFormalization
