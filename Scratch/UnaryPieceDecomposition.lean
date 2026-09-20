import AbelFormalization.Statement

/-!
# Finite unary-piece decompositions

These elementary closure lemmas translate interval decompositions produced by
the final geometric criterion into the project's exact `OMinimal` conclusion.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A set has the exact finite point/open-interval decomposition used in
`OMinimal`. -/
def UnaryPieceDecomposable (s : Set ℝ) : Prop :=
  ∃ (n : ℕ) (pieces : Fin n → UnaryPiece),
    s = ⋃ i, (pieces i).carrier

theorem unaryPieceDecomposable_empty :
    UnaryPieceDecomposable (∅ : Set ℝ) := by
  refine ⟨0, Fin.elim0, ?_⟩
  simp

theorem unaryPieceDecomposable_carrier (piece : UnaryPiece) :
    UnaryPieceDecomposable piece.carrier := by
  refine ⟨1, fun _ ↦ piece, ?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    exact ⟨0, hx⟩
  · rintro ⟨_, hx⟩
    exact hx

theorem UnaryPieceDecomposable.union
    {s t : Set ℝ} (hs : UnaryPieceDecomposable s)
    (ht : UnaryPieceDecomposable t) :
    UnaryPieceDecomposable (s ∪ t) := by
  obtain ⟨n, p, rfl⟩ := hs
  obtain ⟨m, q, rfl⟩ := ht
  refine ⟨n + m, Fin.addCases p q, ?_⟩
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨Fin.castAdd m i, by simpa⟩
    · exact ⟨Fin.natAdd n j, by simpa⟩
  · rintro ⟨k, hk⟩
    exact Fin.addCases
      (fun i hi ↦ Or.inl ⟨i, by simpa using hi⟩)
      (fun j hj ↦ Or.inr ⟨j, by simpa using hj⟩) k hk

theorem unaryPieceDecomposable_singleton (a : ℝ) :
    UnaryPieceDecomposable ({a} : Set ℝ) :=
  unaryPieceDecomposable_carrier (.point a)

theorem unaryPieceDecomposable_Ioo (a b : ℝ) :
    UnaryPieceDecomposable (Ioo a b) :=
  unaryPieceDecomposable_carrier (.bounded a b)

theorem unaryPieceDecomposable_Iio (b : ℝ) :
    UnaryPieceDecomposable (Iio b) :=
  unaryPieceDecomposable_carrier (.leftRay b)

theorem unaryPieceDecomposable_Ioi (a : ℝ) :
    UnaryPieceDecomposable (Ioi a) :=
  unaryPieceDecomposable_carrier (.rightRay a)

theorem unaryPieceDecomposable_univ :
    UnaryPieceDecomposable (Set.univ : Set ℝ) :=
  unaryPieceDecomposable_carrier .whole

theorem unaryPieceDecomposable_Iic (a : ℝ) :
    UnaryPieceDecomposable (Iic a) := by
  have hset : Iic a = Iio a ∪ {a} := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hset]
  exact (unaryPieceDecomposable_Iio a).union
    (unaryPieceDecomposable_singleton a)

theorem unaryPieceDecomposable_Ici (a : ℝ) :
    UnaryPieceDecomposable (Ici a) := by
  have hset : Ici a = {a} ∪ Ioi a := by
    ext x
    simp only [mem_Ici, mem_union, mem_singleton_iff, mem_Ioi]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  rw [hset]
  exact (unaryPieceDecomposable_singleton a).union
    (unaryPieceDecomposable_Ioi a)

theorem unaryPieceDecomposable_Ioc {a b : ℝ} (hab : a < b) :
    UnaryPieceDecomposable (Ioc a b) := by
  rw [show Ioc a b = Ioo a b ∪ {b} by
    ext x
    simp only [mem_Ioc, mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · rintro ⟨hax, hxb⟩
      exact hxb.lt_or_eq.imp (fun h ↦ ⟨hax, h⟩) id
    · rintro (⟨hax, hxb⟩ | rfl)
      · exact ⟨hax, hxb.le⟩
      · exact ⟨hab, le_rfl⟩]
  exact (unaryPieceDecomposable_Ioo a b).union
    (unaryPieceDecomposable_singleton b)

theorem unaryPieceDecomposable_Ico {a b : ℝ} (hab : a < b) :
    UnaryPieceDecomposable (Ico a b) := by
  rw [show Ico a b = {a} ∪ Ioo a b by
    ext x
    simp only [mem_Ico, mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨hax, hxb⟩
      exact hax.eq_or_lt.imp Eq.symm (fun h ↦ ⟨h, hxb⟩)
    · rintro (rfl | ⟨hax, hxb⟩)
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hax.le, hxb⟩]
  exact (unaryPieceDecomposable_singleton a).union
    (unaryPieceDecomposable_Ioo a b)

theorem unaryPieceDecomposable_Icc {a b : ℝ} (hab : a ≤ b) :
    UnaryPieceDecomposable (Icc a b) := by
  rw [show Icc a b = ({a} ∪ Ioo a b) ∪ {b} by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨hax, hxb⟩
      rcases hax.eq_or_lt with rfl | hax
      · exact Or.inl (Or.inl rfl)
      · rcases hxb.lt_or_eq with hxb | rfl
        · exact Or.inl (Or.inr ⟨hax, hxb⟩)
        · exact Or.inr rfl
    · rintro ((rfl | ⟨hax, hxb⟩) | rfl)
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hax.le, hxb.le⟩
      · exact ⟨hab, le_rfl⟩]
  exact ((unaryPieceDecomposable_singleton a).union
    (unaryPieceDecomposable_Ioo a b)).union
      (unaryPieceDecomposable_singleton b)

/-! ## Boolean closure -/

private theorem unaryPieceDecomposable_singleton_inter_carrier
    (a : ℝ) (piece : UnaryPiece) :
    UnaryPieceDecomposable ({a} ∩ piece.carrier) := by
  by_cases ha : a ∈ piece.carrier
  · rw [show {a} ∩ piece.carrier = {a} by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · exact fun h ↦ h.1
      · rintro rfl
        exact ⟨rfl, ha⟩]
    exact unaryPieceDecomposable_singleton a
  · rw [show {a} ∩ piece.carrier = ∅ by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false]
      constructor
      · rintro ⟨rfl, hx⟩
        exact (ha hx).elim
      · intro hx
        exact hx.elim]
    exact unaryPieceDecomposable_empty

/-- The intersection of two elementary unary pieces again has a finite
unary-piece decomposition. -/
theorem unaryPieceDecomposable_carrier_inter_carrier
    (p q : UnaryPiece) :
    UnaryPieceDecomposable (p.carrier ∩ q.carrier) := by
  cases p with
  | point a =>
      change UnaryPieceDecomposable ({a} ∩ q.carrier)
      exact unaryPieceDecomposable_singleton_inter_carrier a q
  | bounded a b =>
      cases q with
      | point c =>
          change UnaryPieceDecomposable (Ioo a b ∩ {c})
          rw [inter_comm]
          exact unaryPieceDecomposable_singleton_inter_carrier c (.bounded a b)
      | bounded c d =>
          change UnaryPieceDecomposable (Ioo a b ∩ Ioo c d)
          rw [show Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d) by
            ext x
            simp only [mem_inter_iff, mem_Ioo, max_lt_iff, lt_min_iff]
            aesop]
          exact unaryPieceDecomposable_Ioo _ _
      | leftRay d =>
          change UnaryPieceDecomposable (Ioo a b ∩ Iio d)
          rw [show Ioo a b ∩ Iio d = Ioo a (min b d) by
            ext x
            simp only [mem_inter_iff, mem_Ioo, mem_Iio, lt_min_iff]
            aesop]
          exact unaryPieceDecomposable_Ioo _ _
      | rightRay c =>
          change UnaryPieceDecomposable (Ioo a b ∩ Ioi c)
          rw [show Ioo a b ∩ Ioi c = Ioo (max a c) b by
            ext x
            simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]
            aesop]
          exact unaryPieceDecomposable_Ioo _ _
      | whole =>
          change UnaryPieceDecomposable (Ioo a b ∩ Set.univ)
          simpa using unaryPieceDecomposable_Ioo a b
  | leftRay b =>
      cases q with
      | point c =>
          change UnaryPieceDecomposable (Iio b ∩ {c})
          rw [inter_comm]
          exact unaryPieceDecomposable_singleton_inter_carrier c (.leftRay b)
      | bounded c d =>
          change UnaryPieceDecomposable (Iio b ∩ Ioo c d)
          rw [show Iio b ∩ Ioo c d = Ioo c (min d b) by
            ext x
            simp only [mem_inter_iff, mem_Iio, mem_Ioo, lt_min_iff]
            aesop]
          exact unaryPieceDecomposable_Ioo _ _
      | leftRay d =>
          change UnaryPieceDecomposable (Iio b ∩ Iio d)
          rw [show Iio b ∩ Iio d = Iio (min b d) by
            ext x
            simp only [mem_inter_iff, mem_Iio, lt_min_iff]]
          exact unaryPieceDecomposable_Iio _
      | rightRay c =>
          change UnaryPieceDecomposable (Iio b ∩ Ioi c)
          rw [show Iio b ∩ Ioi c = Ioo c b by
            ext x
            simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]]
          exact unaryPieceDecomposable_Ioo _ _
      | whole =>
          change UnaryPieceDecomposable (Iio b ∩ Set.univ)
          simpa using unaryPieceDecomposable_Iio b
  | rightRay a =>
      cases q with
      | point c =>
          change UnaryPieceDecomposable (Ioi a ∩ {c})
          rw [inter_comm]
          exact unaryPieceDecomposable_singleton_inter_carrier c (.rightRay a)
      | bounded c d =>
          change UnaryPieceDecomposable (Ioi a ∩ Ioo c d)
          rw [show Ioi a ∩ Ioo c d = Ioo (max c a) d by
            ext x
            simp only [mem_inter_iff, mem_Ioi, mem_Ioo, max_lt_iff]
            aesop]
          exact unaryPieceDecomposable_Ioo _ _
      | leftRay d =>
          change UnaryPieceDecomposable (Ioi a ∩ Iio d)
          rw [show Ioi a ∩ Iio d = Ioo a d by
            ext x
            simp only [mem_inter_iff, mem_Ioi, mem_Iio, mem_Ioo]]
          exact unaryPieceDecomposable_Ioo _ _
      | rightRay c =>
          change UnaryPieceDecomposable (Ioi a ∩ Ioi c)
          rw [show Ioi a ∩ Ioi c = Ioi (max a c) by
            ext x
            simp only [mem_inter_iff, mem_Ioi, max_lt_iff]]
          exact unaryPieceDecomposable_Ioi _
      | whole =>
          change UnaryPieceDecomposable (Ioi a ∩ Set.univ)
          simpa using unaryPieceDecomposable_Ioi a
  | whole =>
      change UnaryPieceDecomposable (Set.univ ∩ q.carrier)
      simpa using unaryPieceDecomposable_carrier q

/-- The complement of one elementary piece has a finite unary-piece
decomposition. -/
theorem unaryPieceDecomposable_compl_carrier (piece : UnaryPiece) :
    UnaryPieceDecomposable piece.carrierᶜ := by
  cases piece with
  | point a =>
      change UnaryPieceDecomposable ({a} : Set ℝ)ᶜ
      rw [show ({a} : Set ℝ)ᶜ = Iio a ∪ Ioi a by
        ext x
        simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Iio,
          mem_Ioi]
        constructor
        · exact lt_or_gt_of_ne
        · rintro (h | h)
          · exact ne_of_lt h
          · exact ne_of_gt h]
      exact (unaryPieceDecomposable_Iio a).union
        (unaryPieceDecomposable_Ioi a)
  | bounded a b =>
      change UnaryPieceDecomposable (Ioo a b)ᶜ
      rw [show (Ioo a b)ᶜ = Iic a ∪ Ici b by
        ext x
        simp only [mem_compl_iff, mem_Ioo, mem_union, mem_Iic, mem_Ici,
          not_and_or, not_lt]]
      exact (unaryPieceDecomposable_Iic a).union
        (unaryPieceDecomposable_Ici b)
  | leftRay b =>
      change UnaryPieceDecomposable (Iio b)ᶜ
      rw [show (Iio b)ᶜ = Ici b by
        ext x
        simp only [mem_compl_iff, mem_Iio, mem_Ici, not_lt]]
      exact unaryPieceDecomposable_Ici b
  | rightRay a =>
      change UnaryPieceDecomposable (Ioi a)ᶜ
      rw [show (Ioi a)ᶜ = Iic a by
        ext x
        simp only [mem_compl_iff, mem_Ioi, mem_Iic, not_lt]]
      exact unaryPieceDecomposable_Iic a
  | whole =>
      change UnaryPieceDecomposable (Set.univ : Set ℝ)ᶜ
      simpa using unaryPieceDecomposable_empty

/-- A finite union of decomposable sets is decomposable. -/
theorem unaryPieceDecomposable_iUnion_fin
    {n : ℕ} (s : Fin n → Set ℝ)
    (hs : ∀ i, UnaryPieceDecomposable (s i)) :
    UnaryPieceDecomposable (⋃ i, s i) := by
  induction n with
  | zero =>
      simpa using unaryPieceDecomposable_empty
  | succ n ih =>
      have hsplit : (⋃ i : Fin (n + 1), s i) =
          s 0 ∪ ⋃ j : Fin n, s j.succ := by
        ext x
        simp only [mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i ↦ x ∈ s i →
              x ∈ s 0 ∨ ∃ j : Fin n, x ∈ s j.succ)
            (fun h ↦ Or.inl h)
            (fun j h ↦ Or.inr ⟨j, h⟩) i hi
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨0, hx⟩
          · exact ⟨j.succ, hj⟩
      rw [hsplit]
      exact (hs 0).union
        (ih (fun j ↦ s j.succ) (fun j ↦ hs j.succ))

/-- Finite unary-piece decompositions are closed under intersection. -/
theorem UnaryPieceDecomposable.inter
    {s t : Set ℝ} (hs : UnaryPieceDecomposable s)
    (ht : UnaryPieceDecomposable t) :
    UnaryPieceDecomposable (s ∩ t) := by
  obtain ⟨n, p, rfl⟩ := hs
  obtain ⟨m, q, rfl⟩ := ht
  rw [show (⋃ i, (p i).carrier) ∩ (⋃ j, (q j).carrier) =
      ⋃ i, ⋃ j, (p i).carrier ∩ (q j).carrier by
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    aesop]
  apply unaryPieceDecomposable_iUnion_fin
  intro i
  apply unaryPieceDecomposable_iUnion_fin
  intro j
  exact unaryPieceDecomposable_carrier_inter_carrier (p i) (q j)

/-- Finite unary-piece decompositions are closed under complement. -/
theorem UnaryPieceDecomposable.compl
    {s : Set ℝ} (hs : UnaryPieceDecomposable s) :
    UnaryPieceDecomposable sᶜ := by
  obtain ⟨n, p, rfl⟩ := hs
  induction n with
  | zero =>
      simpa using unaryPieceDecomposable_univ
  | succ n ih =>
      have hsplit : (⋃ i : Fin (n + 1), (p i).carrier) =
          (p 0).carrier ∪ ⋃ j : Fin n, (p j.succ).carrier := by
        ext x
        simp only [mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i ↦ x ∈ (p i).carrier →
              x ∈ (p 0).carrier ∨
                ∃ j : Fin n, x ∈ (p j.succ).carrier)
            (fun h ↦ Or.inl h)
            (fun j h ↦ Or.inr ⟨j, h⟩) i hi
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨0, hx⟩
          · exact ⟨j.succ, hj⟩
      rw [hsplit, compl_union]
      exact (unaryPieceDecomposable_compl_carrier (p 0)).inter
        (ih (fun j ↦ p j.succ))

theorem UnaryPieceDecomposable.diff
    {s t : Set ℝ} (hs : UnaryPieceDecomposable s)
    (ht : UnaryPieceDecomposable t) :
    UnaryPieceDecomposable (s \ t) := by
  rw [sdiff_eq]
  exact hs.inter ht.compl

end AbelFormalization
