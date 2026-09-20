import AbelFormalization.CharbonnelSardianCertificateAlgebra

/-!
# Padding Sardian approximation certificates to a common hidden depth

`CharbonnelSardianCertificateAlgebra` combines certificates once their
hidden arities agree.  This file supplies the preceding step of Wilkie's
Lemma 3.7.  An unused final positive parameter is appended to every padded
constituent and to its modulus.  The two asymmetric approximation clauses
are unchanged because deleting that final parameter recovers the old
section, while bounded modulus vectors make the new parameter positive.

Successor padding is iterated to any larger hidden arity.  Two independent
certificates can therefore be padded to the maximum of their hidden arities
and combined by the existing equal-depth union operation.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## One final unused positive parameter -/

/-- Reconstruct a parameter vector from its initial segment and last
coordinate. -/
@[simp]
theorem charbonnelAppendLastParameter_init_last {k : ℕ}
    (epsilon : RealEuclidean ((k + 1) + 1)) :
    charbonnelAppendLastParameter (Fin.init epsilon)
        (epsilon (Fin.last (k + 1))) = epsilon := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [charbonnelAppendLastParameter_last]
  · have hj : j.castSucc = Fin.castAdd 1 j := Fin.ext rfl
    rw [hj]
    simp [charbonnelAppendLastParameter, Fin.init, hj]

/-- The tail of a parameter vector is obtained by appending its last
coordinate to the tail of its initial segment. -/
theorem charbonnelParameterTail_eq_appendLastParameter_init_last
    {K : ℕ} (epsilon : RealEuclidean (((K + 1) + 1) + 1)) :
    CharbonnelModulus.parameterTail epsilon =
      charbonnelAppendLastParameter
        (CharbonnelModulus.parameterTail (Fin.init epsilon))
        (epsilon (Fin.last ((K + 1) + 1))) := by
  calc
    CharbonnelModulus.parameterTail epsilon =
        CharbonnelModulus.parameterTail
          (charbonnelAppendLastParameter (Fin.init epsilon)
            (epsilon (Fin.last ((K + 1) + 1)))) := by
      rw [charbonnelAppendLastParameter_init_last]
    _ = realEuclideanAppend
        (CharbonnelModulus.parameterTail (Fin.init epsilon))
        (fun _ : Fin 1 ↦ epsilon (Fin.last ((K + 1) + 1))) :=
      charbonnelParameterTail_appendLastParameter _ _
    _ = charbonnelAppendLastParameter
        (CharbonnelModulus.parameterTail (Fin.init epsilon))
        (epsilon (Fin.last ((K + 1) + 1))) := rfl

/-- At equal source and target depth, parameter padding is the identity. -/
theorem charbonnelParameterPrefixLinearMap_refl
    {n q : ℕ} (v : RealEuclidean (n + (q + 1))) :
    charbonnelParameterPrefixLinearMap n q q (Nat.le_refl q) v = v := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [charbonnelParameterPrefixLinearMap, realEuclideanTakeLeft,
      realEuclideanTakeRight]

@[simp]
theorem charbonnelParameterPad_refl
    {n q : ℕ} (A : Set (RealEuclidean (n + (q + 1)))) :
    charbonnelParameterPad (Nat.le_refl q) A = A := by
  ext v
  rw [mem_charbonnelParameterPad_iff,
    charbonnelParameterPrefixLinearMap_refl]
  constructor
  · exact fun hv ↦ hv.1
  · intro hv
    refine ⟨hv, ?_⟩
    intro i hi
    exact (Nat.not_lt_of_ge hi i.isLt).elim

/-- Appending one new final parameter commutes with padding from `q` to
`K`: the old padded section is recovered by deleting the final parameter,
and membership additionally asks that the new parameter be positive. -/
theorem mem_charbonnelParameterPad_appendLastParameter_iff
    {n q K : ℕ} (hqK : q ≤ K)
    {A : Set (RealEuclidean (n + (q + 1)))}
    (x : RealEuclidean n) (epsilon : RealEuclidean (K + 1))
    (eta : ℝ) :
    realEuclideanAppend x
        (charbonnelAppendLastParameter epsilon eta) ∈
        charbonnelParameterPad
          (hqK.trans (Nat.le_succ K)) A ↔
      realEuclideanAppend x epsilon ∈
        charbonnelParameterPad hqK A ∧
        0 < eta := by
  rw [mem_charbonnelParameterPad_append_iff
      (hqK.trans (Nat.le_succ K)) (A := A) x
        (charbonnelAppendLastParameter epsilon eta),
    mem_charbonnelParameterPad_append_iff hqK (A := A) x epsilon]
  have hprefix :
      (fun i : Fin (q + 1) ↦
        charbonnelAppendLastParameter epsilon eta
          (Fin.castLE
            (Nat.succ_le_succ (hqK.trans (Nat.le_succ K))) i)) =
      (fun i : Fin (q + 1) ↦
        epsilon (Fin.castLE (Nat.succ_le_succ hqK) i)) := by
    funext i
    let j : Fin (K + 1) :=
      Fin.castLE (Nat.succ_le_succ hqK) i
    have hij :
        Fin.castLE
            (Nat.succ_le_succ (hqK.trans (Nat.le_succ K))) i =
          Fin.castAdd 1 j := by
      apply Fin.ext
      rfl
    rw [hij]
    simp [j, charbonnelAppendLastParameter]
  rw [hprefix]
  constructor
  · rintro ⟨hA, htrailing⟩
    refine ⟨⟨hA, ?_⟩, ?_⟩
    · intro i hi
      have hpositive := htrailing (Fin.castAdd 1 i) (by
        simpa using hi)
      simpa [charbonnelAppendLastParameter] using hpositive
    · have hpositive := htrailing (Fin.last (K + 1)) (by
        have hqK' : q + 1 ≤ K + 1 := Nat.succ_le_succ hqK
        simpa using hqK')
      simpa only [charbonnelAppendLastParameter_last] using hpositive
  · rintro ⟨⟨hA, htrailing⟩, heta⟩
    refine ⟨hA, ?_⟩
    intro i hi
    let positive : ∀ i : Fin ((K + 1) + 1),
        q < i.val →
        0 < charbonnelAppendLastParameter epsilon eta i := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · intro _
        simpa only [charbonnelAppendLastParameter_last] using heta
      · intro hj
        have hpositive := htrailing j hj
        have hcast : j.castSucc = Fin.castAdd 1 j := Fin.ext rfl
        rw [hcast]
        simpa [charbonnelAppendLastParameter] using hpositive
    exact positive i hi

/-- The preceding formula specialized to padding one exact common depth to
its successor. -/
theorem mem_charbonnelParameterPad_succ_appendLastParameter_iff
    {n K : ℕ} {A : Set (RealEuclidean (n + (K + 1)))}
    (x : RealEuclidean n) (epsilon : RealEuclidean (K + 1))
    (eta : ℝ) :
    realEuclideanAppend x
        (charbonnelAppendLastParameter epsilon eta) ∈
        charbonnelParameterPad (Nat.le_succ K) A ↔
      realEuclideanAppend x epsilon ∈ A ∧ 0 < eta := by
  have h := mem_charbonnelParameterPad_appendLastParameter_iff
    (n := n) (q := K) (K := K) (Nat.le_refl K)
    (A := A) x epsilon eta
  simpa only [charbonnelParameterPad_refl] using h

/-! ## Successor padding for constituents and finite families -/

namespace CharbonnelPaddedSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Regard a padded constituent at depth `K` as one at depth `K+1`. -/
def succPad
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    CharbonnelPaddedSardianConstituent G order n (K + 1) :=
  { hiddenArity := piece.hiddenArity
    hiddenArity_le := piece.hiddenArity_le.trans (Nat.le_succ K)
    constituent := piece.constituent }

/-- Successor padding of a constituent carrier is the existing
unused-positive-parameter padding operation. -/
theorem carrier_succPad
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    piece.succPad.carrier =
      charbonnelParameterPad (Nat.le_succ K) piece.carrier := by
  ext v
  let x : RealEuclidean n := realEuclideanTakeLeft v
  let parameters : RealEuclidean ((K + 1) + 1) :=
    realEuclideanTakeRight v
  let epsilon : RealEuclidean (K + 1) := Fin.init parameters
  let eta : ℝ := parameters (Fin.last (K + 1))
  have hparameters :
      charbonnelAppendLastParameter epsilon eta = parameters := by
    exact charbonnelAppendLastParameter_init_last parameters
  have hv :
      realEuclideanAppend x
          (charbonnelAppendLastParameter epsilon eta) = v := by
    rw [hparameters]
    exact realEuclideanAppend_takeLeft_takeRight v
  rw [← hv]
  change
    realEuclideanAppend x
        (charbonnelAppendLastParameter epsilon eta) ∈
          charbonnelParameterPad
            (piece.hiddenArity_le.trans (Nat.le_succ K))
            piece.constituent.carrier ↔
      realEuclideanAppend x
        (charbonnelAppendLastParameter epsilon eta) ∈
          charbonnelParameterPad (Nat.le_succ K)
            (charbonnelParameterPad piece.hiddenArity_le
              piece.constituent.carrier)
  rw [mem_charbonnelParameterPad_appendLastParameter_iff
      (n := n) (q := piece.hiddenArity) (K := K)
      piece.hiddenArity_le (A := piece.constituent.carrier) x epsilon eta,
    mem_charbonnelParameterPad_succ_appendLastParameter_iff
      (n := n) (K := K)
      (A := charbonnelParameterPad piece.hiddenArity_le
        piece.constituent.carrier) x epsilon eta]

end CharbonnelPaddedSardianConstituent

namespace CharbonnelFiniteSardianFamily

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Pad every member of a finite common-depth family by one unused final
positive parameter. -/
def succPad (family : CharbonnelFiniteSardianFamily G order n K) :
    CharbonnelFiniteSardianFamily G order n (K + 1) :=
  ⟨family.visible_pos,
    family.constituents.map
      CharbonnelPaddedSardianConstituent.succPad⟩

/-- The carrier of the successor-padded family is the parameter padding of
the old finite union. -/
theorem carrier_succPad
    (family : CharbonnelFiniteSardianFamily G order n K) :
    family.succPad.carrier =
      charbonnelParameterPad (Nat.le_succ K) family.carrier := by
  ext v
  change
    (∃ piece ∈ family.constituents.map
        CharbonnelPaddedSardianConstituent.succPad,
      v ∈ piece.carrier) ↔
      v ∈ charbonnelParameterPad (Nat.le_succ K) family.carrier
  rw [mem_charbonnelParameterPad_iff]
  constructor
  · rintro ⟨padded, hpadded, hv⟩
    rcases List.mem_map.mp hpadded with ⟨piece, hpiece, rfl⟩
    rw [CharbonnelPaddedSardianConstituent.carrier_succPad,
      mem_charbonnelParameterPad_iff] at hv
    exact ⟨⟨piece, hpiece, hv.1⟩, hv.2⟩
  · rintro ⟨hv, htrailing⟩
    change ∃ piece ∈ family.constituents,
      charbonnelParameterPrefixLinearMap n K (K + 1)
          (Nat.le_succ K) v ∈ piece.carrier at hv
    obtain ⟨piece, hpiece, hvPiece⟩ := hv
    refine ⟨piece.succPad,
      List.mem_map.mpr ⟨piece, hpiece, rfl⟩, ?_⟩
    rw [CharbonnelPaddedSardianConstituent.carrier_succPad,
      mem_charbonnelParameterPad_iff]
    exact ⟨hvPiece, htrailing⟩

end CharbonnelFiniteSardianFamily

/-! ## Successor padding preserves the approximation clauses -/

namespace CharbonnelModulus

/-- Extend a modulus by one unused final positive parameter.  The fixed
upper bound `1` is immaterial; its role is only to make the new nested bound
positive. -/
def appendUnit {k : ℕ} (modulus : CharbonnelModulus k) :
    CharbonnelModulus (k + 1) :=
  .step modulus (fun _ ↦ (1 : ℝ)) (fun _ _ ↦ zero_lt_one)

@[simp]
theorem isBounded_appendUnit_iff {k : ℕ}
    (modulus : CharbonnelModulus k)
    (epsilon : RealEuclidean ((k + 1) + 1)) :
    modulus.appendUnit.IsBounded epsilon ↔
      modulus.IsBounded (Fin.init epsilon) ∧
        0 < epsilon (Fin.last (k + 1)) ∧
        epsilon (Fin.last (k + 1)) < 1 :=
  Iff.rfl

/-- Approximation from below is unchanged after adding one unused final
positive parameter. -/
theorem ApproximatesFromBelow.succParameterPad
    {n K : ℕ} {modulus : CharbonnelModulus (K + 1)}
    {T : Set (RealEuclidean (n + (K + 1)))}
    {A : Set (RealEuclidean n)}
    (h : ApproximatesFromBelow modulus T A) :
    ApproximatesFromBelow modulus.appendUnit
      (charbonnelParameterPad (Nat.le_succ K) T) A := by
  intro epsilon hepsilon x hx
  have hbounded := (isBounded_appendUnit_iff modulus epsilon).mp hepsilon
  have hxPad := hx
  rw [charbonnelParameterTail_eq_appendLastParameter_init_last,
    mem_charbonnelParameterPad_succ_appendLastParameter_iff] at hxPad
  obtain ⟨y, hy, hxy⟩ :=
    h (Fin.init epsilon) hbounded.1 x hxPad.1
  exact ⟨y, hy, by simpa [Fin.init] using hxy⟩

/-- Approximation from above on bounded sets is unchanged after adding one
unused final positive parameter. -/
theorem ApproximatesFromAboveOnBoundedSets.succParameterPad
    {n K : ℕ} {modulus : CharbonnelModulus (K + 1)}
    {A : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + (K + 1)))}
    (h : ApproximatesFromAboveOnBoundedSets modulus A T) :
    ApproximatesFromAboveOnBoundedSets modulus.appendUnit A
      (charbonnelParameterPad (Nat.le_succ K) T) := by
  intro epsilon hepsilon x hx hnorm
  have hbounded := (isBounded_appendUnit_iff modulus epsilon).mp hepsilon
  have hnorm' : ‖x‖ < ((Fin.init epsilon) 0)⁻¹ := by
    simpa [Fin.init] using hnorm
  obtain ⟨y, hxy, hy⟩ :=
    h (Fin.init epsilon) hbounded.1 x hx hnorm'
  refine ⟨y, by simpa [Fin.init] using hxy, ?_⟩
  rw [charbonnelParameterTail_eq_appendLastParameter_init_last,
    mem_charbonnelParameterPad_succ_appendLastParameter_iff]
  exact ⟨hy, hbounded.2.1⟩

/-- Wilkie's asymmetric closure/boundary approximation predicate is
preserved by one unused final parameter. -/
theorem IsClosureBoundaryApproximation.succParameterPad
    {n K : ℕ} {modulus : CharbonnelModulus (K + 1)}
    {T : Set (RealEuclidean (n + (K + 1)))}
    {A : Set (RealEuclidean n)}
    (h : IsClosureBoundaryApproximation modulus T A) :
    IsClosureBoundaryApproximation modulus.appendUnit
      (charbonnelParameterPad (Nat.le_succ K) T) A :=
  ⟨h.1.succParameterPad, h.2.succParameterPad⟩

end CharbonnelModulus

/-! ## Indexed certificate padding and unequal-depth union -/

namespace CharbonnelSardianApproximationCertificate

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n : ℕ} {A B : Set (RealEuclidean n)}

namespace AtHiddenArity

/-- Pad an indexed certificate by one unused final positive parameter. -/
def succPad {K : ℕ}
    (certificate : AtHiddenArity G order n A K) :
    AtHiddenArity G order n A (K + 1) := by
  let family := certificate.family.succPad
  let modulus := certificate.modulus.appendUnit
  refine
    { order_pos := certificate.order_pos
      family := family
      modulus := modulus
      approximates := ?_ }
  rw [show family.carrier =
      charbonnelParameterPad (Nat.le_succ K)
        certificate.family.carrier by
    exact CharbonnelFiniteSardianFamily.carrier_succPad certificate.family]
  exact certificate.approximates.succParameterPad

/-- Iterate successor padding by `extra` unused final parameters. -/
def padRight {K : ℕ}
    (certificate : AtHiddenArity G order n A K) :
    (extra : ℕ) → AtHiddenArity G order n A (K + extra)
  | 0 => certificate
  | extra + 1 => (padRight certificate extra).succPad

/-- Pad an indexed certificate to any specified larger hidden arity. -/
def padTo {K L : ℕ} (hKL : K ≤ L)
    (certificate : AtHiddenArity G order n A K) :
    AtHiddenArity G order n A L :=
  (Nat.add_sub_of_le hKL) ▸ certificate.padRight (L - K)

/-- Pad two indexed certificates to the maximum of their hidden arities and
apply the existing equal-depth union construction. -/
def unionPadded {K L : ℕ}
    (left : AtHiddenArity G order n A K)
    (right : AtHiddenArity G order n B L) :
    AtHiddenArity G order n (A ∪ B)
      (charbonnelCommonHiddenArity K L) :=
  (left.padTo (Nat.le_max_left K L)).union
    (right.padTo (Nat.le_max_right K L))

end AtHiddenArity

/-- Two Sardian approximation certificates with arbitrary independently
chosen hidden depths combine after padding both depths to their maximum. -/
def unionOfAnyHiddenArity
    (left : CharbonnelSardianApproximationCertificate G order n A)
    (right : CharbonnelSardianApproximationCertificate G order n B) :
    CharbonnelSardianApproximationCertificate G order n (A ∪ B) :=
  (left.toAtHiddenArity.unionPadded right.toAtHiddenArity).toCertificate

@[simp]
theorem commonHiddenArity_unionOfAnyHiddenArity
    (left : CharbonnelSardianApproximationCertificate G order n A)
    (right : CharbonnelSardianApproximationCertificate G order n B) :
    (unionOfAnyHiddenArity left right).commonHiddenArity =
      charbonnelCommonHiddenArity left.commonHiddenArity
        right.commonHiddenArity :=
  rfl

end CharbonnelSardianApproximationCertificate

end AbelFormalization
