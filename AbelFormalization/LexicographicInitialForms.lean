import AbelFormalization.WeightedNormalization
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual finite-dimensional lexicographic initial forms

The public weight space is `Lex (Fin h → ℤ)`, with the coordinate order on
`Fin h` used by mathlib's `Pi.Lex`. The minimum is taken over the actual finite
monomial support. The head-tail theorem is a proved identity of coefficient
filters, rather than a recursive definition of the lexicographic initial.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommSemiring R] {h : ℕ}

/-- The minimum actual lexicographic vector weight among supported monomials;
the zero polynomial is assigned the zero vector. -/
def lexicographicMinimumWeight (ω : ι → Fin h → ℤ) (f : MvPolynomial ι R) :
    Lex (Fin h → ℤ) := by
  classical
  exact if hs : f.support.Nonempty then
    f.support.inf' hs (Finsupp.weight (fun i => toLex (ω i))) else 0

@[simp]
theorem lexicographicMinimumWeight_zero (ω : ι → Fin h → ℤ) :
    lexicographicMinimumWeight ω (0 : MvPolynomial ι R) = 0 := by
  simp [lexicographicMinimumWeight]

theorem lexicographicMinimumWeight_le (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) {d : ι →₀ ℕ} (hd : d ∈ f.support) :
    lexicographicMinimumWeight ω f ≤ Finsupp.weight (fun i => toLex (ω i)) d := by
  classical
  have hs : f.support.Nonempty := ⟨d, hd⟩
  simp only [lexicographicMinimumWeight, dite_eq_left hs]
  exact Finset.inf'_le _ hd

theorem exists_support_lexicographicWeight_eq_minimum (ω : ι → Fin h → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ d ∈ f.support,
      Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f := by
  classical
  have hs : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  obtain ⟨d, hd, hle⟩ :=
    (Finset.inf'_le_iff hs (f := Finsupp.weight (fun i => toLex (ω i)))).mp le_rfl
  refine ⟨d, hd, le_antisymm ?_ (lexicographicMinimumWeight_le ω f hd)⟩
  simpa only [lexicographicMinimumWeight, dite_eq_left hs] using hle

/-- The actual least-vector-weight component, defined using mathlib's
multivariate polynomial component operator over the lexicographic group. -/
def lexicographicInitialForm (ω : ι → Fin h → ℤ) (f : MvPolynomial ι R) :
    MvPolynomial ι R :=
  MvPolynomial.weightedHomogeneousComponent (fun i => toLex (ω i))
    (lexicographicMinimumWeight ω f) f

theorem lexicographicInitialForm_coeff (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) (d : ι →₀ ℕ) :
    (lexicographicInitialForm ω f).coeff d =
      if Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f
      then f.coeff d else 0 := by
  classical
  exact MvPolynomial.coeff_weightedHomogeneousComponent _ _ _

theorem lexicographicInitialForm_support (ω : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) :
    (lexicographicInitialForm ω f).support =
      f.support.filter (fun d =>
        Finsupp.weight (fun i => toLex (ω i)) d = lexicographicMinimumWeight ω f) := by
  classical
  exact MvPolynomial.support_weightedHomogeneousComponent _ _

@[simp]
theorem lexicographicInitialForm_zero (ω : ι → Fin h → ℤ) :
    lexicographicInitialForm ω (0 : MvPolynomial ι R) = 0 := by
  simp [lexicographicInitialForm]

theorem lexicographicInitialForm_ne_zero (ω : ι → Fin h → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) : lexicographicInitialForm ω f ≠ 0 := by
  classical
  obtain ⟨d, hd, hweight⟩ := exists_support_lexicographicWeight_eq_minimum ω hf
  intro hz
  have hc : f.coeff d = 0 := by
    simpa only [lexicographicInitialForm_coeff, ite_eq_left hweight,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (fun p : MvPolynomial ι R => p.coeff d) hz
  exact (MvPolynomial.mem_support_iff.mp hd) hc

/-- With no weight coordinates, all monomials have the same weight and the
initial form leaves the polynomial unchanged. -/
@[simp]
theorem lexicographicInitialForm_zero_dim (ω : ι → Fin 0 → ℤ)
    (f : MvPolynomial ι R) : lexicographicInitialForm ω f = f := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [lexicographicInitialForm_coeff]
  exact ite_eq_left (Subsingleton.elim _ _)

/-- The actual `Fin`-indexed lexicographic order first compares the new head
coordinate, and compares the tails precisely when the heads agree. -/
theorem finLex_cons_lt_iff (a b : ℤ) (u v : Fin h → ℤ) :
    toLex (Fin.cons a u : Fin (h + 1) → ℤ) <
      toLex (Fin.cons b v : Fin (h + 1) → ℤ) ↔
      a < b ∨ a = b ∧ toLex u < toLex v := by
  constructor
  · rintro ⟨j, hbefore, hlt⟩
    cases j using Fin.cases with
    | zero => exact Or.inl (by simpa only [Pi.toLex_apply, Fin.cons_zero] using hlt)
    | succ j =>
        right
        refine ⟨?_, j, ?_, ?_⟩
        · simpa only [Pi.toLex_apply, Fin.cons_zero] using hbefore 0 (Fin.succ_pos j)
        · intro k hk
          simpa only [Pi.toLex_apply, Fin.cons_succ] using
            hbefore k.succ (Fin.succ_lt_succ_iff.mpr hk)
        · simpa only [Pi.toLex_apply, Fin.cons_succ] using hlt
  · rintro (hab | ⟨hab, j, hbefore, hlt⟩)
    · refine ⟨0, ?_, ?_⟩
      · intro k hk
        exact (Fin.not_lt_zero k hk).elim
      · simpa only [Pi.toLex_apply, Fin.cons_zero] using hab
    · refine ⟨j.succ, ?_, ?_⟩
      · intro k hk
        cases k using Fin.cases with
        | zero => simpa only [Pi.toLex_apply, Fin.cons_zero] using hab
        | succ k =>
            simpa only [Pi.toLex_apply, Fin.cons_succ] using
              hbefore k (Fin.succ_lt_succ_iff.mp hk)
      · simpa only [Pi.toLex_apply, Fin.cons_succ] using hlt

set_option backward.isDefEq.respectTransparency false in
theorem finLex_cons_le_iff (a b : ℤ) (u v : Fin h → ℤ) :
    toLex (Fin.cons a u : Fin (h + 1) → ℤ) ≤
      toLex (Fin.cons b v : Fin (h + 1) → ℤ) ↔
      a < b ∨ a = b ∧ toLex u ≤ toLex v := by
  have hlt := finLex_cons_lt_iff a b u v
  rw [le_iff_lt_or_eq, hlt]
  simp only [le_iff_lt_or_eq, toLex_inj, Fin.cons_inj, and_or_left, or_assoc]

/-- Evaluation of a lexicographic weight at one coordinate is an additive
homomorphism; this statement does not assert that it preserves lex order. -/
def lexicographicCoordinate (j : Fin h) : Lex (Fin h → ℤ) →+ ℤ where
  toFun x := ofLex x j
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lexicographicWeight_apply (ω : ι → Fin h → ℤ)
    (d : ι →₀ ℕ) (j : Fin h) :
    ofLex (Finsupp.weight (fun i => toLex (ω i)) d) j =
      Finsupp.weight (fun i => ω i j) d := by
  change lexicographicCoordinate j (Finsupp.weight (fun i => toLex (ω i)) d) = _
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]
  rfl

/-- Computing a vector monomial weight commutes with splitting its head and
tail coordinates. -/
theorem lexicographicWeight_cons (ω : ι → ℤ) (ν : ι → Fin h → ℤ)
    (d : ι →₀ ℕ) :
    Finsupp.weight (fun i => toLex (Fin.cons (ω i) (ν i))) d =
      toLex (Fin.cons (Finsupp.weight ω d)
        (ofLex (Finsupp.weight (fun i => toLex (ν i)) d)) : Fin (h + 1) → ℤ) := by
  apply ofLex.injective
  funext j
  rw [lexicographicWeight_apply, ofLex_toLex]
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero]
  | succ j => simp only [Fin.cons_succ, lexicographicWeight_apply]

/-- The lexicographic minimum is obtained by first selecting the least head
weight, and then minimizing the tail on that actual nonzero component. -/
theorem lexicographicMinimumWeight_cons (ω : ι → ℤ) (ν : ι → Fin h → ℤ)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    lexicographicMinimumWeight (fun i => Fin.cons (ω i) (ν i)) f =
      toLex (Fin.cons (minimumSupportWeight ω f)
        (ofLex (lexicographicMinimumWeight ν
          (MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f)))) := by
  classical
  let g := MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f
  have hg : g ≠ 0 := weightedHomogeneousComponent_minimum_ne_zero ω hf
  have hsupport : g.support =
      f.support.filter (fun d => Finsupp.weight ω d = minimumSupportWeight ω f) :=
    MvPolynomial.support_weightedHomogeneousComponent _ _
  change lexicographicMinimumWeight (fun i => Fin.cons (ω i) (ν i)) f =
    toLex (Fin.cons (minimumSupportWeight ω f) (ofLex (lexicographicMinimumWeight ν g)))
  apply le_antisymm
  · obtain ⟨d, hdg, htail⟩ := exists_support_lexicographicWeight_eq_minimum ν hg
    have hd := Finset.mem_filter.mp (hsupport ▸ hdg)
    have hmin := lexicographicMinimumWeight_le (fun i => Fin.cons (ω i) (ν i)) f hd.1
    simpa only [lexicographicWeight_cons, hd.2, htail] using hmin
  · obtain ⟨d, hd, hweight⟩ :=
      exists_support_lexicographicWeight_eq_minimum (fun i => Fin.cons (ω i) (ν i)) hf
    rw [← hweight, lexicographicWeight_cons, finLex_cons_le_iff]
    have hhead := minimumSupportWeight_le ω f hd
    rcases lt_or_eq_of_le hhead with hlt | heq
    · exact Or.inl hlt
    · right
      refine ⟨heq, ?_⟩
      have hdg : d ∈ g.support := by
        rw [hsupport]
        exact Finset.mem_filter.mpr ⟨hd, heq.symm⟩
      exact lexicographicMinimumWeight_le ν g hdg

/-- Element-level head-tail compatibility for the actual lexicographic
initial form. This equality remains valid over rings with zero divisors. -/
theorem lexicographicInitialForm_cons (ω : ι → ℤ) (ν : ι → Fin h → ℤ)
    (f : MvPolynomial ι R) :
    lexicographicInitialForm (fun i => Fin.cons (ω i) (ν i)) f =
      lexicographicInitialForm ν
        (MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f) := by
  classical
  by_cases hf : f = 0
  · subst f
    simp
  apply MvPolynomial.ext
  intro d
  rw [lexicographicInitialForm_coeff, lexicographicInitialForm_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    lexicographicMinimumWeight_cons ω ν hf, lexicographicWeight_cons]
  simp only [toLex_inj, Fin.cons_inj, ofLex_inj]
  by_cases hhead : Finsupp.weight ω d = minimumSupportWeight ω f <;>
    by_cases htail : Finsupp.weight (fun i => toLex (ν i)) d =
      lexicographicMinimumWeight ν
        (MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f) <;>
    simp [hhead, htail]

end AbelFormalization
