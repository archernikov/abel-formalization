import AbelFormalization.LexicographicInitialIdealPrincipalQuotient
import AbelFormalization.PrincipalIdealSaturationQuotient
import AbelFormalization.RankOneIdealIterationBaseChange
import AbelFormalization.TerminalReindexedGlobalArtinianDescent

set_option autoImplicit false

/-!
# The terminal ideal iteration after a principal coefficient quotient

This file packages the recursion used after the minimal-prime localization
stage.  The generic first theorem says that a tail of the initial-ideal
iteration commutes with a coefficient map as soon as initial formation
commutes on the intermediate ideals occurring along that tail.

For the quotient `B -> B/(b)`, the needed compatibility follows from the
principal-quotient theorem whenever every intermediate `J(I_j)` lies in the
sandwich

`(C b) K <= J(I_j) <= K`,

where `K` is multihomogeneous and saturated by `C b`.  Thus the shifted
images of the source iteration are literally the terminal iteration over
`B/(b)`.  The final theorems turn a fixed quotient iterate first into equality
of the two quotient images and then, given the two interval hypotheses, into
fixedness of the source iterate itself.
-/

noncomputable section

namespace AbelFormalization

universe u v w

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## A generic shifted base-change recursion -/

section Generic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {n h : ℕ}

/-- A tail of the initial-ideal iteration commutes with a ring map if the
automorphisms commute with that map and full initial formation commutes on
the mapped ideals occurring along the tail.

The target seed is `map (J(I_j1))`.  Consequently its zeroth initial iterate
is the image of `I_(j1+1)`, which accounts for the shift by one in the
conclusion. -/
theorem lexicographicInitialIdealIteration_map_shifted_of_initial_compatibility
    (weight : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) R)
    (J' : MvPolynomial (Fin n) S ≃+* MvPolynomial (Fin n) S)
    (f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S)
    (hJ : f.comp J.toRingHom = J'.toRingHom.comp f)
    (Q : Ideal (MvPolynomial (Fin n) R)) (j₁ : ℕ)
    (hinitial : ∀ k : ℕ,
      (lexicographicInitialIdeal weight
          ((lexicographicInitialIdealIteration weight J Q (j₁ + k)).map
            J.toRingHom)).map f =
        lexicographicInitialIdeal weight
          (((lexicographicInitialIdealIteration weight J Q (j₁ + k)).map
            J.toRingHom).map f)) :
    ∀ k : ℕ,
      (lexicographicInitialIdealIteration weight J Q (j₁ + k + 1)).map f =
        lexicographicInitialIdealIteration weight J'
          (((lexicographicInitialIdealIteration weight J Q j₁).map
            J.toRingHom).map f) k := by
  intro k
  induction k with
  | zero =>
      change
        (lexicographicInitialIdeal weight
            ((lexicographicInitialIdealIteration weight J Q j₁).map
              J.toRingHom)).map f =
          lexicographicInitialIdeal weight
            (((lexicographicInitialIdealIteration weight J Q j₁).map
              J.toRingHom).map f)
      simpa only [Nat.add_zero] using hinitial 0
  | succ k ih =>
      change
        (lexicographicInitialIdeal weight
            ((lexicographicInitialIdealIteration weight J Q
              (j₁ + k + 1)).map J.toRingHom)).map f =
          lexicographicInitialIdeal weight
            ((lexicographicInitialIdealIteration weight J'
              (((lexicographicInitialIdealIteration weight J Q j₁).map
                J.toRingHom).map f) k).map J'.toRingHom)
      calc
        (lexicographicInitialIdeal weight
            ((lexicographicInitialIdealIteration weight J Q
              (j₁ + k + 1)).map J.toRingHom)).map f =
          lexicographicInitialIdeal weight
            (((lexicographicInitialIdealIteration weight J Q
              (j₁ + k + 1)).map J.toRingHom).map f) := by
            simpa only [Nat.add_succ] using hinitial (k + 1)
        _ = lexicographicInitialIdeal weight
            (((lexicographicInitialIdealIteration weight J Q
              (j₁ + k + 1)).map f).map J'.toRingHom) := by
            rw [Ideal.map_map, Ideal.map_map, hJ]
        _ = lexicographicInitialIdeal weight
            ((lexicographicInitialIdealIteration weight J'
              (((lexicographicInitialIdealIteration weight J Q j₁).map
                J.toRingHom).map f) k).map J'.toRingHom) := by
            rw [ih]

/-- If two polynomial automorphisms intertwine a coefficient map, fixedness
of the image of an ideal implies equality between the images of that ideal
and of its transform. -/
theorem ideal_map_transform_eq_map_of_target_fixed
    (J : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) R)
    (J' : MvPolynomial (Fin n) S ≃+* MvPolynomial (Fin n) S)
    (f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S)
    (hJ : f.comp J.toRingHom = J'.toRingHom.comp f)
    (N : Ideal (MvPolynomial (Fin n) R))
    (hfixed : (N.map f).map J'.toRingHom = N.map f) :
    (N.map J.toRingHom).map f = N.map f := by
  calc
    (N.map J.toRingHom).map f =
        N.map (f.comp J.toRingHom) := by rw [Ideal.map_map]
    _ = N.map (J'.toRingHom.comp f) := by rw [hJ]
    _ = (N.map f).map J'.toRingHom := by rw [Ideal.map_map]
    _ = N.map f := hfixed

end Generic

/-! ## Terminal principal-quotient data -/

variable {B : Type u} [CommRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- The coefficientwise polynomial quotient map modulo `(b)`. -/
abbrev terminalReindexedPrincipalQuotientMap (b : B) :
    MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (B ⧸ Ideal.span {b}) :=
  mvPolynomialPrincipalCoefficientQuotientMap (Fin n) b

/-- The natural seed for the shifted quotient recursion: reduce `J(I_j1)`
modulo `(b)`.  Its initial ideal is the reduction of `I_(j1+1)`. -/
abbrev terminalReindexedPrincipalQuotientSeed
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B) :
    Ideal (MvPolynomial (Fin n) (B ⧸ Ideal.span {b})) :=
  (((lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d Time e)
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv Q j₁).map
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom).map
    (terminalReindexedPrincipalQuotientMap (n := n) b))

/-- The exact interval hypothesis needed by principal-quotient initial
compatibility along the shifted source tail. -/
def TerminalReindexedMappedTailSandwich
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B)
    (K : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  ∀ k : ℕ,
    Ideal.span {MvPolynomial.C b} * K ≤
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + k)).map
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv.toRingHom ∧
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + k)).map
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv.toRingHom ≤ K

/-- Companion interval hypothesis for the source iterates themselves.  It is
only needed when quotient equality is lifted back to literal source
fixedness. -/
def TerminalReindexedTailSandwich
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B)
    (K : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  ∀ k : ℕ,
    Ideal.span {MvPolynomial.C b} * K ≤
        lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + k) ∧
      lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + k) ≤ K

/-! ## Exact shifted recursion modulo `(b)` -/

/-- Under the principal sandwich on all intermediate `J(I_j)`, the shifted
images of the source terminal iteration are exactly the terminal iteration
over `B/(b)` with seed `map (J(I_j1))`. -/
theorem terminalReindexedPrincipalQuotientIteration_map_shifted
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B)
    (K : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (terminalReindexedMultiDegree d Time e i))))
    (hKsat : ∀ P : MvPolynomial (Fin n) B,
      MvPolynomial.C b * P ∈ K → P ∈ K)
    (hsandwich : TerminalReindexedMappedTailSandwich
      d Time e Q j₁ b K) :
    ∀ k : ℕ,
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
        (terminalReindexedPrincipalQuotientMap (n := n) b) =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
        (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k := by
  let weight := terminalReindexedMultiDegree d Time e
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let quotientJ := (terminalReindexedGlobalStirlingEquiv
    (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
  let coefficientQuotient : B →+* B ⧸ Ideal.span {b} :=
    Ideal.Quotient.mk (Ideal.span {b})
  let q : MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (B ⧸ Ideal.span {b}) :=
    MvPolynomial.map coefficientQuotient
  have hcommute : q.comp sourceJ.toRingHom =
      quotientJ.toRingHom.comp q := by
    simpa only [q, coefficientQuotient, sourceJ, quotientJ] using
      map_comp_terminalReindexedGlobalStirlingEquiv d Time e
        coefficientQuotient
  have hinitial : ∀ k : ℕ,
      (lexicographicInitialIdeal weight
          ((lexicographicInitialIdealIteration weight sourceJ Q
            (j₁ + k)).map sourceJ.toRingHom)).map q =
        lexicographicInitialIdeal weight
          (((lexicographicInitialIdealIteration weight sourceJ Q
            (j₁ + k)).map sourceJ.toRingHom).map q) := by
    intro k
    exact lexicographicInitialIdeal_map_principalQuotient
      b weight
      ((lexicographicInitialIdealIteration weight sourceJ Q
        (j₁ + k)).map sourceJ.toRingHom)
      K (hsandwich k).2 hK hKsat (hsandwich k).1
  intro k
  have htail :=
    lexicographicInitialIdealIteration_map_shifted_of_initial_compatibility
      weight sourceJ quotientJ q hcommute Q j₁ hinitial k
  simpa only [weight, sourceJ, quotientJ, q, coefficientQuotient,
    terminalReindexedPrincipalQuotientMap,
    mvPolynomialPrincipalCoefficientQuotientMap,
    terminalReindexedPrincipalQuotientSeed,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-! ## Ordinary homogeneity of the quotient seed -/

/-- The shifted quotient seed is ordinary homogeneous, so the lower
Krull-dimension terminal stabilization theorem applies to it. -/
theorem terminalReindexedPrincipalQuotientSeed_ordinaryHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (terminalReindexedOrdinaryDegree n i : ℤ))))
    (j₁ : ℕ) (b : B) :
    (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule
        (B ⧸ Ideal.span {b})
        (fun i => (terminalReindexedOrdinaryDegree n i : ℤ))) := by
  let ordinaryDegree := terminalReindexedOrdinaryDegree n
  let weight := terminalReindexedMultiDegree d Time e
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let I := lexicographicInitialIdealIteration weight sourceJ Q
  have hJordinary : ∀ N : Ideal (MvPolynomial (Fin n) B),
      N.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (N.map sourceJ.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) := by
    intro N hN
    change N.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ : Fin n => (1 : ℤ))) at hN
    have hmap := terminalReindexedGlobalStirlingEquiv_map_isHomogeneous
      (B := B) d Time e N hN
    change (N.map sourceJ.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ : Fin n => (1 : ℤ)))
    simpa only [sourceJ] using hmap
  have hI : (I j₁).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) := by
    exact lexicographicInitialIdealIteration_ordinaryHomogeneous
      ordinaryDegree weight sourceJ Q
      (by simpa only [ordinaryDegree] using hQ) hJordinary j₁
  have hJI : ((I j₁).map sourceJ.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) :=
    hJordinary (I j₁) hI
  have hseed := mvPolynomial_ideal_map_isHomogeneous
    (Ideal.Quotient.mk (Ideal.span {b}))
    (fun i => (ordinaryDegree i : ℤ))
    ((I j₁).map sourceJ.toRingHom) hJI
  simpa only [terminalReindexedPrincipalQuotientSeed,
    terminalReindexedPrincipalQuotientMap,
    mvPolynomialPrincipalCoefficientQuotientMap,
    ordinaryDegree, weight, sourceJ, I] using hseed

/-! ## Fixedness in the quotient and lifting through the interval -/

/-- If the quotient iterate corresponding to a shifted source ideal is fixed,
the quotient images of the source ideal and its `J`-image are equal. -/
theorem terminalReindexedPrincipalQuotient_fixed_image_of_correspondence
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ k : ℕ) (b : B)
    (hcorrespond :
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
        (terminalReindexedPrincipalQuotientMap (n := n) b) =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
        (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k)
    (hfixed :
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
          (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k).map
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv.toRingHom =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
        (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k) :
    ((lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom).map
      (terminalReindexedPrincipalQuotientMap (n := n) b) =
    (lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
      (terminalReindexedPrincipalQuotientMap (n := n) b) := by
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let quotientJ := (terminalReindexedGlobalStirlingEquiv
    (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
  let q := terminalReindexedPrincipalQuotientMap (n := n) b
  let N := lexicographicInitialIdealIteration
    (terminalReindexedMultiDegree d Time e) sourceJ Q (j₁ + 1 + k)
  have hcommute : q.comp sourceJ.toRingHom =
      quotientJ.toRingHom.comp q := by
    simpa only [q, terminalReindexedPrincipalQuotientMap,
      mvPolynomialPrincipalCoefficientQuotientMap, sourceJ, quotientJ] using
      map_comp_terminalReindexedGlobalStirlingEquiv d Time e
        (Ideal.Quotient.mk (Ideal.span {b}))
  apply ideal_map_transform_eq_map_of_target_fixed
    sourceJ quotientJ q hcommute N
  calc
    (N.map q).map quotientJ.toRingHom =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) quotientJ
          (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k).map
            quotientJ.toRingHom := by
          rw [show N.map q =
            lexicographicInitialIdealIteration
              (terminalReindexedMultiDegree d Time e) quotientJ
              (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k by
            simpa only [N, q, sourceJ, quotientJ] using hcorrespond]
    _ = lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) quotientJ
          (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k := by
        simpa only [quotientJ] using hfixed
    _ = N.map q := by
        symm
        simpa only [N, q, sourceJ, quotientJ] using hcorrespond

/-- All-in-one image-level consequence: the principal sandwich produces the
tail correspondence, and a fixed quotient iterate then gives equality of the
two quotient images at the corresponding source index. -/
theorem terminalReindexedPrincipalQuotient_fixed_image
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B)
    (K : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (terminalReindexedMultiDegree d Time e i))))
    (hKsat : ∀ P : MvPolynomial (Fin n) B,
      MvPolynomial.C b * P ∈ K → P ∈ K)
    (hsandwich : TerminalReindexedMappedTailSandwich
      d Time e Q j₁ b K)
    (k : ℕ)
    (hfixed :
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
          (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k).map
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv.toRingHom =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
        (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k) :
    ((lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv.toRingHom).map
      (terminalReindexedPrincipalQuotientMap (n := n) b) =
    (lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)).map
      (terminalReindexedPrincipalQuotientMap (n := n) b) := by
  apply terminalReindexedPrincipalQuotient_fixed_image_of_correspondence
    d Time e Q j₁ k b
  · exact terminalReindexedPrincipalQuotientIteration_map_shifted
      d Time e Q j₁ b K hK hKsat hsandwich k
  · exact hfixed

/-- If the source ideal and its transform both lie in the saturated
principal interval, fixedness in the quotient lifts to literal fixedness of
the corresponding source iterate. -/
theorem terminalReindexedPrincipalQuotient_fixed_of_sandwich
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j₁ : ℕ) (b : B)
    (K : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (terminalReindexedMultiDegree d Time e i))))
    (hKsat : ∀ P : MvPolynomial (Fin n) B,
      MvPolynomial.C b * P ∈ K → P ∈ K)
    (hsourceSandwich : TerminalReindexedTailSandwich
      d Time e Q j₁ b K)
    (hmappedSandwich : TerminalReindexedMappedTailSandwich
      d Time e Q j₁ b K)
    (k : ℕ)
    (hfixed :
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
          (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k).map
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv.toRingHom =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
        (terminalReindexedPrincipalQuotientSeed d Time e Q j₁ b) k) :
    let I := lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d Time e)
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv Q (j₁ + 1 + k)
    I.map (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv.toRingHom = I := by
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let q := terminalReindexedPrincipalQuotientMap (n := n) b
  let I := lexicographicInitialIdealIteration
    (terminalReindexedMultiDegree d Time e) sourceJ Q (j₁ + 1 + k)
  have himage : (I.map sourceJ.toRingHom).map q = I.map q := by
    simpa only [I, sourceJ, q] using
      terminalReindexedPrincipalQuotient_fixed_image
        d Time e Q j₁ b K hK hKsat hmappedSandwich k hfixed
  have hsource := hsourceSandwich (k + 1)
  have hmapped := hmappedSandwich (k + 1)
  apply eq_of_map_eq_of_span_singleton_mul_le_of_le_of_saturated
    q (mvPolynomialPrincipalCoefficientQuotientMap_surjective
      (Fin n) b)
    (MvPolynomial.C b) K (I.map sourceJ.toRingHom) I
    (mvPolynomialPrincipalCoefficientQuotientMap_ker (Fin n) b)
    hKsat
  · simpa only [I, sourceJ, Nat.add_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmapped.1
  · simpa only [I, sourceJ, Nat.add_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmapped.2
  · simpa only [I, sourceJ, Nat.add_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource.1
  · simpa only [I, sourceJ, Nat.add_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource.2
  · exact himage

end AbelFormalization
