import AbelFormalization.LexicographicInitialIdealComponents
import AbelFormalization.LexicographicInitialIdealLocalization
import AbelFormalization.RankOneIdealWindowRecurrence
import AbelFormalization.TerminalReindexedGlobalArtinianDescent

set_option autoImplicit false

/-!
# Sandwich recurrence for terminal reindexed initial ideals

After localization and contraction, the manuscript places one iterate between
the coefficient multiple `span {C b} * K` and the contracted ideal `K`.
Both endpoints are homogeneous for the full terminal multigrading and fixed
by the terminal Stirling automorphism.  Monotonicity of full initial ideals
therefore keeps every later iterate, and every intermediate Stirling image,
inside the same interval.

The first part of this file records the generic order-theoretic argument.
The final part specializes it to the concrete terminal automorphism and the
principal coefficient multiple supplied by denominator clearing.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Generic homogeneity and monotonicity lemmas -/

/-- Full lexicographic initial formation is monotone in the source ideal. -/
theorem lexicographicInitialIdeal_mono
    {R : Type u} {ι : Type v} [CommRing R] {h : ℕ}
    (weight : ι → Fin h → ℤ)
    {I K : Ideal (MvPolynomial ι R)} (hIK : I ≤ K) :
    lexicographicInitialIdeal weight I ≤
      lexicographicInitialIdeal weight K := by
  apply Ideal.span_mono
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨P, hIK hP, rfl⟩

/-- Coefficient maps commute with weighted homogeneous components for an
arbitrary additive grading monoid. -/
theorem mvPolynomial_map_weightedHomogeneousComponent_general
    {R : Type u} {S : Type v} {σ : Type w} {M : Type z}
    [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [DecidableEq M]
    (f : R →+* S) (weight : σ → M) (degree : M)
    (P : MvPolynomial σ R) :
    MvPolynomial.map f
        (MvPolynomial.weightedHomogeneousComponent weight degree P) =
      MvPolynomial.weightedHomogeneousComponent weight degree
        (MvPolynomial.map f P) := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_map,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> simp_all

/-- Contraction along a coefficient map preserves homogeneity for every
weighted polynomial grading.  No injectivity or surjectivity hypothesis on
the coefficient map is needed. -/
theorem mvPolynomial_ideal_comap_isHomogeneous
    {R : Type u} {S : Type v} {σ : Type w} {M : Type z}
    [CommRing R] [CommRing S]
    [AddCommMonoid M] [DecidableEq M]
    (f : R →+* S) (weight : σ → M)
    (I : Ideal (MvPolynomial σ S))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule S weight)) :
    (I.comap (MvPolynomial.map f)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight) := by
  intro degree P hP
  change MvPolynomial.map f P ∈ I at hP
  rw [← DirectSum.Decomposition.decompose'_eq]
  rw [MvPolynomial.weightedDecomposition.decompose'_apply]
  change MvPolynomial.map f
      (MvPolynomial.weightedHomogeneousComponent weight degree P) ∈ I
  rw [mvPolynomial_map_weightedHomogeneousComponent_general]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem
    S weight hI hP degree

/-- Multiplying a weighted-homogeneous polynomial ideal by a principal
coefficient ideal preserves homogeneity for the same grading. -/
theorem principalCoefficientMultiple_isHomogeneous
    {R : Type u} {ι : Type v} {M : Type w}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (weight : ι → M) (b : R) (K : Ideal (MvPolynomial ι R))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight)) :
    (Ideal.span {MvPolynomial.C b} * K).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight) := by
  have hconstant : (Ideal.span {MvPolynomial.C b}).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight) := by
    apply Ideal.homogeneous_span
    intro P hP
    have hPC : P = MvPolynomial.C b := by
      simpa only [Set.mem_singleton_iff] using hP
    subst P
    exact ⟨0, MvPolynomial.isWeightedHomogeneous_C weight b⟩
  exact hconstant.mul hK

/-! ## An invariant interval for one descent step -/

/-- A ring automorphism carries every ideal between two invariant endpoint
ideals to another ideal between the same endpoints. -/
theorem ideal_map_interval_of_interval
    {A : Type u} [CommRing A]
    (J : A ≃+* A) {D N K : Ideal A}
    (hDinv : D.map J.toRingHom = D)
    (hKinv : K.map J.toRingHom = K)
    (hDN : D ≤ N) (hNK : N ≤ K) :
    D ≤ N.map J.toRingHom ∧ N.map J.toRingHom ≤ K := by
  constructor
  · calc
      D = D.map J.toRingHom := hDinv.symm
      _ ≤ N.map J.toRingHom := Ideal.map_mono hDN
  · calc
      N.map J.toRingHom ≤ K.map J.toRingHom := Ideal.map_mono hNK
      _ = K := hKinv

/-- If the endpoints of an invariant interval are homogeneous for the full
lexicographic grading, applying the automorphism and then taking the full
initial ideal preserves that interval. -/
theorem lexicographicInitialIdeal_map_interval_of_interval
    {R : Type u} {ι : Type v} [CommRing R] {h : ℕ}
    (weight : ι → Fin h → ℤ)
    (J : MvPolynomial ι R ≃+* MvPolynomial ι R)
    {D N K : Ideal (MvPolynomial ι R)}
    (hDhom : D.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i ↦ toLex (weight i))))
    (hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i ↦ toLex (weight i))))
    (hDinv : D.map J.toRingHom = D)
    (hKinv : K.map J.toRingHom = K)
    (hDN : D ≤ N) (hNK : N ≤ K) :
    D ≤ lexicographicInitialIdeal weight (N.map J.toRingHom) ∧
      lexicographicInitialIdeal weight (N.map J.toRingHom) ≤ K := by
  obtain ⟨hDmapN, hNmapK⟩ :=
    ideal_map_interval_of_interval J hDinv hKinv hDN hNK
  constructor
  · calc
      D = lexicographicInitialIdeal weight D :=
        (lexicographicInitialIdeal_eq_of_homogeneous weight D hDhom).symm
      _ ≤ lexicographicInitialIdeal weight (N.map J.toRingHom) :=
        lexicographicInitialIdeal_mono weight hDmapN
  · calc
      lexicographicInitialIdeal weight (N.map J.toRingHom) ≤
          lexicographicInitialIdeal weight K :=
        lexicographicInitialIdeal_mono weight hNmapK
      _ = K := lexicographicInitialIdeal_eq_of_homogeneous weight K hKhom

/-! ## Shifted iteration bounds and permanence -/

/-- Every term of the ideal iteration is homogeneous for the full vector
grading used to define its lexicographic initial ideal. -/
theorem lexicographicInitialIdealIteration_isHomogeneous
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    (lexicographicInitialIdealIteration weight J Q j).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (weight i))) := by
  cases j with
  | zero =>
      exact lexicographicInitialIdeal_isHomogeneous weight Q
  | succ j =>
      exact lexicographicInitialIdeal_isHomogeneous weight
        ((lexicographicInitialIdealIteration weight J Q j).map
          J.toRingHom)

/-- Once one term lies in a homogeneous invariant interval, every shifted
later term lies in the same interval. -/
theorem lexicographicInitialIdealIteration_shifted_interval
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q D K : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hDhom : D.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (weight i))))
    (hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (weight i))))
    (hDinv : D.map J.toRingHom = D)
    (hKinv : K.map J.toRingHom = K)
    (hDbase : D ≤ lexicographicInitialIdealIteration weight J Q j₀)
    (hbaseK : lexicographicInitialIdealIteration weight J Q j₀ ≤ K) :
    ∀ k : ℕ,
      D ≤ lexicographicInitialIdealIteration weight J Q (j₀ + k) ∧
        lexicographicInitialIdealIteration weight J Q (j₀ + k) ≤ K := by
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero] using And.intro hDbase hbaseK
  | succ k ih =>
      rw [Nat.add_succ, lexicographicInitialIdealIteration_succ]
      exact lexicographicInitialIdeal_map_interval_of_interval
        weight J hDhom hKhom hDinv hKinv ih.1 ih.2

/-- The intermediate automorphism images of all shifted later terms also
lie in the same invariant interval.  This is the form used before passing
the successor recurrence to a coefficient quotient. -/
theorem lexicographicInitialIdealIteration_shifted_map_interval
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q D K : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hDhom : D.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (weight i))))
    (hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (weight i))))
    (hDinv : D.map J.toRingHom = D)
    (hKinv : K.map J.toRingHom = K)
    (hDbase : D ≤ lexicographicInitialIdealIteration weight J Q j₀)
    (hbaseK : lexicographicInitialIdealIteration weight J Q j₀ ≤ K) :
    ∀ k : ℕ,
      D ≤ (lexicographicInitialIdealIteration
          weight J Q (j₀ + k)).map J.toRingHom ∧
        (lexicographicInitialIdealIteration
          weight J Q (j₀ + k)).map J.toRingHom ≤ K := by
  intro k
  obtain ⟨hDk, hkK⟩ :=
    lexicographicInitialIdealIteration_shifted_interval
      weight J Q D K j₀ hDhom hKhom hDinv hKinv
        hDbase hbaseK k
  exact ideal_map_interval_of_interval J hDinv hKinv hDk hkK

/-- A fixed point of the one-step recurrence remains fixed at every shifted
later index. -/
theorem lexicographicInitialIdealIteration_permanent_of_step_fixed
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hfixed :
      lexicographicInitialIdeal weight
          ((lexicographicInitialIdealIteration weight J Q j₀).map
            J.toRingHom) =
        lexicographicInitialIdealIteration weight J Q j₀) :
    ∀ k : ℕ,
      lexicographicInitialIdealIteration weight J Q (j₀ + k) =
        lexicographicInitialIdealIteration weight J Q j₀ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, lexicographicInitialIdealIteration_succ, ih,
        hfixed]

/-- Equality of one term with its successor is permanent. -/
theorem lexicographicInitialIdealIteration_permanent_of_eq_succ
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hfixed :
      lexicographicInitialIdealIteration weight J Q (j₀ + 1) =
        lexicographicInitialIdealIteration weight J Q j₀) :
    ∀ k : ℕ,
      lexicographicInitialIdealIteration weight J Q (j₀ + k) =
        lexicographicInitialIdealIteration weight J Q j₀ := by
  apply lexicographicInitialIdealIteration_permanent_of_step_fixed
    weight J Q j₀
  simpa only [lexicographicInitialIdealIteration_succ] using hfixed

/-- If an iterate is fixed by the automorphism itself, its intrinsic
lexicographic homogeneity makes it a permanent fixed point of the recurrence. -/
theorem lexicographicInitialIdealIteration_permanent_of_map_fixed
    {B : Type u} [CommRing B] {n h : ℕ}
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hfixed :
      (lexicographicInitialIdealIteration weight J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration weight J Q j₀) :
    ∀ k : ℕ,
      lexicographicInitialIdealIteration weight J Q (j₀ + k) =
        lexicographicInitialIdealIteration weight J Q j₀ := by
  apply lexicographicInitialIdealIteration_permanent_of_step_fixed
    weight J Q j₀
  rw [hfixed]
  exact lexicographicInitialIdeal_eq_of_homogeneous weight _
    (lexicographicInitialIdealIteration_isHomogeneous
      weight J Q j₀)

/-! ## The concrete terminal principal-multiple interval -/

variable {B : Type u} [CommRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- The principal coefficient multiple of a terminal-weight-homogeneous
ideal is homogeneous for the same terminal multigrading. -/
theorem terminalReindexedPrincipalMultiple_isHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    (b : B) (K : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)))) :
    (Ideal.span {MvPolynomial.C b} * K).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))) :=
  principalCoefficientMultiple_isHomogeneous
    (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)) b K hK

/-- The terminal Stirling automorphism fixes a principal coefficient
multiple whenever it fixes the ideal being multiplied. -/
theorem terminalReindexedPrincipalMultiple_map_eq
    (e : TerminalFiniteReindex (n := n) d Time)
    (b : B) (K : Ideal (MvPolynomial (Fin n) B))
    (hKinv :
      K.map (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom = K) :
    (Ideal.span {MvPolynomial.C b} * K).map
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv.toRingHom =
      Ideal.span {MvPolynomial.C b} * K := by
  let Jalg := terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e
  have hC : Jalg (MvPolynomial.C b) = MvPolynomial.C b := by
    simpa only [MvPolynomial.C_eq_algebraMap] using Jalg.commutes b
  have hC' : Jalg.toRingEquiv.toRingHom (MvPolynomial.C b) =
      MvPolynomial.C b := by
    calc
      Jalg.toRingEquiv.toRingHom (MvPolynomial.C b) =
          Jalg (MvPolynomial.C b) := rfl
      _ = MvPolynomial.C b := hC
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hC', hKinv]

/-- A denominator sandwich at one terminal iterate persists for all shifted
later iterates. -/
theorem terminalReindexedLexicographicInitialIdealIteration_shifted_sandwich
    (e : TerminalFiniteReindex (n := n) d Time)
    (b : B) (K Q : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))))
    (hKinv :
      K.map (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom = K)
    (hDbase : Ideal.span {MvPolynomial.C b} * K ≤
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q j₀)
    (hbaseK : lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q j₀ ≤ K) :
    ∀ k : ℕ,
      Ideal.span {MvPolynomial.C b} * K ≤
          lexicographicInitialIdealIteration
            (terminalReindexedMultiDegree d Time e)
            (terminalReindexedGlobalStirlingEquiv
              (R := B) d Time e).toRingEquiv Q (j₀ + k) ∧
        lexicographicInitialIdealIteration
            (terminalReindexedMultiDegree d Time e)
            (terminalReindexedGlobalStirlingEquiv
              (R := B) d Time e).toRingEquiv Q (j₀ + k) ≤ K := by
  exact lexicographicInitialIdealIteration_shifted_interval
    (terminalReindexedMultiDegree d Time e)
    (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    Q (Ideal.span {MvPolynomial.C b} * K) K j₀
    (terminalReindexedPrincipalMultiple_isHomogeneous
      d Time e b K hKhom)
    hKhom
    (terminalReindexedPrincipalMultiple_map_eq
      d Time e b K hKinv)
    hKinv hDbase hbaseK

/-- Every intermediate terminal-Stirling image of a shifted later iterate
also satisfies the same denominator sandwich. -/
theorem terminalReindexedLexicographicInitialIdealIteration_shifted_map_sandwich
    (e : TerminalFiniteReindex (n := n) d Time)
    (b : B) (K Q : Ideal (MvPolynomial (Fin n) B)) (j₀ : ℕ)
    (hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))))
    (hKinv :
      K.map (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom = K)
    (hDbase : Ideal.span {MvPolynomial.C b} * K ≤
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q j₀)
    (hbaseK : lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q j₀ ≤ K) :
    ∀ k : ℕ,
      Ideal.span {MvPolynomial.C b} * K ≤
          (lexicographicInitialIdealIteration
            (terminalReindexedMultiDegree d Time e)
            (terminalReindexedGlobalStirlingEquiv
              (R := B) d Time e).toRingEquiv Q (j₀ + k)).map
                (terminalReindexedGlobalStirlingEquiv
                  (R := B) d Time e).toRingEquiv.toRingHom ∧
        (lexicographicInitialIdealIteration
            (terminalReindexedMultiDegree d Time e)
            (terminalReindexedGlobalStirlingEquiv
              (R := B) d Time e).toRingEquiv Q (j₀ + k)).map
                (terminalReindexedGlobalStirlingEquiv
                  (R := B) d Time e).toRingEquiv.toRingHom ≤ K := by
  exact lexicographicInitialIdealIteration_shifted_map_interval
    (terminalReindexedMultiDegree d Time e)
    (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    Q (Ideal.span {MvPolynomial.C b} * K) K j₀
    (terminalReindexedPrincipalMultiple_isHomogeneous
      d Time e b K hKhom)
    hKhom
    (terminalReindexedPrincipalMultiple_map_eq
      d Time e b K hKinv)
    hKinv hDbase hbaseK

end AbelFormalization
