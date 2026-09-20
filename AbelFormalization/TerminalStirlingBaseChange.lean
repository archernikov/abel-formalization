import AbelFormalization.TerminalReindexedWindowStirling
import AbelFormalization.RankOneIdealGlobalArtinianDescent

set_option autoImplicit false

/-!
# Coefficient base change for the terminal Stirling automorphism

The simultaneous signed-Stirling substitution is defined over `ℤ`: its only
scalar coefficients are integer casts of signed Stirling numbers.  It
therefore commutes with every homomorphism of commutative coefficient rings.
This file records that naturality first for the block presentation, then for
an arbitrary finite reindexing, and finally at the level of mapped ideals.

For the canonical product decomposition of an Artinian coefficient ring, we
also identify each ideal component with extension along the corresponding
coefficient projection.  Combining this description with naturality gives
the exact `map_factor` equality required by
`RankOneGlobalArtinianDescentData`.

No injectivity or surjectivity hypothesis on the coefficient homomorphism is
used.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

/-! ## Naturality before and after finite reindexing -/

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {Block : Type w} (d : Block → ℕ) (Time : Type z)

/-- Mapping coefficients after the global terminal Stirling action is the
same ring homomorphism as first mapping coefficients and then applying the
action over the target ring. -/
theorem map_comp_terminalGlobalStirlingEquiv
    (f : R →+* S) :
    (MvPolynomial.map f).comp
        (terminalGlobalStirlingEquiv R Block d Time).toRingHom =
      (terminalGlobalStirlingEquiv S Block d Time).toRingHom.comp
        (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · rintro (⟨b, i⟩ | t)
    · simp
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      split <;> simp_all
    · simp

/-- Pointwise form of `map_comp_terminalGlobalStirlingEquiv`. -/
theorem terminalGlobalStirlingEquiv_map
    (f : R →+* S) (P : CentralPolynomial R Block d Time) :
    MvPolynomial.map f
        (terminalGlobalStirlingEquiv R Block d Time P) =
      terminalGlobalStirlingEquiv S Block d Time
        (MvPolynomial.map f P) :=
  RingHom.congr_fun (map_comp_terminalGlobalStirlingEquiv d Time f) P

variable {h n : ℕ} (dFin : Fin h → ℕ) (FiniteTime : Type z)

/-- Coefficient base change commutes with the terminal Stirling action after
conjugating through any fixed enumeration of the terminal variables. -/
theorem terminalReindexedGlobalStirlingEquiv_map
    (e : TerminalFiniteReindex (n := n) dFin FiniteTime)
    (f : R →+* S) (P : MvPolynomial (Fin n) R) :
    MvPolynomial.map f
        (terminalReindexedGlobalStirlingEquiv
          (R := R) dFin FiniteTime e P) =
      terminalReindexedGlobalStirlingEquiv
        (R := S) dFin FiniteTime e (MvPolynomial.map f P) := by
  change
    MvPolynomial.map f
        (MvPolynomial.rename e.symm
          (terminalGlobalStirlingEquiv R (Fin h) dFin FiniteTime
            (MvPolynomial.rename e P))) =
      MvPolynomial.rename e.symm
        (terminalGlobalStirlingEquiv S (Fin h) dFin FiniteTime
          (MvPolynomial.rename e (MvPolynomial.map f P)))
  rw [MvPolynomial.map_rename,
    terminalGlobalStirlingEquiv_map,
    MvPolynomial.map_rename]

/-- Ring-homomorphism form of reindexed terminal Stirling naturality. -/
theorem map_comp_terminalReindexedGlobalStirlingEquiv
    (e : TerminalFiniteReindex (n := n) dFin FiniteTime)
    (f : R →+* S) :
    (MvPolynomial.map f).comp
        (terminalReindexedGlobalStirlingEquiv
          (R := R) dFin FiniteTime e).toRingHom =
      (terminalReindexedGlobalStirlingEquiv
        (R := S) dFin FiniteTime e).toRingHom.comp
          (MvPolynomial.map f) :=
  RingHom.ext fun P ↦
    terminalReindexedGlobalStirlingEquiv_map dFin FiniteTime e f P

/-- Naturality after extension of an ideal.  This is the generic algebraic
identity underlying every factorwise `map_factor` proof. -/
theorem terminalReindexedGlobalStirlingEquiv_ideal_map
    (e : TerminalFiniteReindex (n := n) dFin FiniteTime)
    (f : R →+* S) (I : Ideal (MvPolynomial (Fin n) R)) :
    (I.map
        (terminalReindexedGlobalStirlingEquiv
          (R := R) dFin FiniteTime e).toRingHom).map
        (MvPolynomial.map f) =
      (I.map (MvPolynomial.map f)).map
        (terminalReindexedGlobalStirlingEquiv
          (R := S) dFin FiniteTime e).toRingHom := by
  simpa only [Ideal.map_map] using
    congrArg
      (fun φ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S ↦
        I.map φ)
      (map_comp_terminalReindexedGlobalStirlingEquiv
        dFin FiniteTime e f)

/-! ## The canonical Artinian factor projections -/

/-- The coefficient homomorphism from an Artinian ring to one component of
its canonical product decomposition. -/
noncomputable def artinianLocalFactorCoefficientHom
    (B : Type*) [CommRing B] [IsArtinianRing B]
    (m : MaximalSpectrum B) :
    B →+* artinianLocalFactor B m :=
  (Pi.evalRingHom
      (fun q : MaximalSpectrum B ↦ artinianLocalFactor B q) m).comp
    (artinianLocalFactorEquiv B).toRingHom

/-- Evaluating the polynomial product equivalence at a factor is exactly
coefficient extension along `artinianLocalFactorCoefficientHom`. -/
@[simp]
theorem artinianLocalFactorPolynomialEquiv_apply_at
    (B : Type*) [CommRing B] [IsArtinianRing B]
    {sigma : Type*} (P : MvPolynomial sigma B)
    (m : MaximalSpectrum B) :
    artinianLocalFactorPolynomialEquiv B sigma P m =
      MvPolynomial.map (artinianLocalFactorCoefficientHom B m) P := by
  change
    MvPolynomial.map
        (Pi.evalRingHom
          (fun q : MaximalSpectrum B ↦ artinianLocalFactor B q) m)
        (MvPolynomial.map (artinianLocalFactorEquiv B).toRingHom P) =
      MvPolynomial.map (artinianLocalFactorCoefficientHom B m) P
  rw [MvPolynomial.map_map]
  rfl

/-- Each component of the Artinian polynomial-ideal decomposition is plain
extension of the ideal along its coefficient projection. -/
theorem artinianLocalFactorPolynomialIdealEquiv_apply_eq_map
    (B : Type*) [CommRing B] [IsArtinianRing B]
    {sigma : Type*} (I : Ideal (MvPolynomial sigma B))
    (m : MaximalSpectrum B) :
    artinianLocalFactorPolynomialIdealEquiv B sigma I m =
      I.map (MvPolynomial.map (artinianLocalFactorCoefficientHom B m)) := by
  have hcomp :
      (Pi.evalRingHom
        (fun q : MaximalSpectrum B ↦
          MvPolynomial sigma (artinianLocalFactor B q)) m).comp
          (artinianLocalFactorPolynomialEquiv B sigma).toRingHom =
        MvPolynomial.map (artinianLocalFactorCoefficientHom B m) := by
    apply RingHom.ext
    intro P
    exact artinianLocalFactorPolynomialEquiv_apply_at B P m
  change
    (I.map (artinianLocalFactorPolynomialEquiv B sigma).toRingHom).map
        (Pi.evalRingHom
          (fun q : MaximalSpectrum B ↦
            MvPolynomial sigma (artinianLocalFactor B q)) m) =
      I.map (MvPolynomial.map (artinianLocalFactorCoefficientHom B m))
  rw [Ideal.map_map, hcomp]

/-! ## The `map_factor` identity -/

/-- The concrete reindexed terminal Stirling automorphism commutes with every
canonical Artinian factor projection at the level of ideals.  With the
global and local `J` fields chosen to be the displayed ring equivalences,
this theorem has exactly the type of
`RankOneGlobalArtinianDescentData.map_factor`. -/
theorem artinianLocalFactorPolynomialIdealEquiv_map_terminalStirling
    (B : Type*) [CommRing B] [IsArtinianRing B]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type z)
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) B))
    (m : MaximalSpectrum B) :
    artinianLocalFactorPolynomialIdealEquiv B (Fin n)
        (I.map
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv.toRingHom) m =
      (artinianLocalFactorPolynomialIdealEquiv B (Fin n) I m).map
        (terminalReindexedGlobalStirlingEquiv
          (R := artinianLocalFactor B m) d Time e).toRingEquiv.toRingHom := by
  rw [artinianLocalFactorPolynomialIdealEquiv_apply_eq_map,
    artinianLocalFactorPolynomialIdealEquiv_apply_eq_map]
  exact terminalReindexedGlobalStirlingEquiv_ideal_map
    d Time e (artinianLocalFactorCoefficientHom B m) I

end AbelFormalization
