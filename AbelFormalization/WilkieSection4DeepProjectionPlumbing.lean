import AbelFormalization.WilkieSection4DeepProjectionTower
import AbelFormalization.WilkieSection4ProjectionTowerAssembly

/-!
# Projecting full-dimensional deep covers to bounded closed lifts

A deep projection-coherent cover can be projected one final coordinate at a
time.  This file records the endpoint bookkeeping which turns deep covers in
every full ambient dimension into the bounded deep-cover property used by the
Section 4 projection tower.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Changing only the parenthesized expression for the hidden arity does not
change the existential projection. -/
private theorem realEuclideanExistentialProjection_coordinateReindex_finCongr
    {n q r : ℕ} (h : r = q)
    (B : Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection
        (realEuclideanCoordinateReindex
          (finCongr (congrArg (fun d ↦ n + d) h)) '' B) =
      realEuclideanExistentialProjection B := by
  subst r
  simp [realEuclideanCoordinateReindex]

/-- Full-dimensional deep covers of bounded closed sets supply the deep
projection-coherent covers of every bounded projected closed lift. -/
theorem wilkieBoundedDeepProjectionCoherentCellCoverProperty_of_fullClosedDeepCovers
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hfull : ∀ {m : ℕ} {B : Set (RealEuclidean (m + 1))},
      IsClosed B → B ∈ charbonnelClosure S (m + 1) →
      Nonempty (CharbonnelFiniteDeepProjectionCoherentCellCover S
        (wilkieOpenCube (m + 1)) (wilkieBoundedImage B))) :
    WilkieBoundedDeepProjectionCoherentCellCoverProperty S := by
  intro n q hn
  induction q generalizing n with
  | zero =>
      intro B hBclosed hBmem
      obtain ⟨cover⟩ := hfull (m := n) hBclosed hBmem
      simpa only [Nat.add_zero, realEuclideanExistentialProjection_zero] using
        (show Nonempty
          (CharbonnelFiniteDeepProjectionCoherentCellCover S
            (wilkieOpenCube (n + 1)) (wilkieBoundedImage B)) from ⟨cover⟩)
  | succ q ih =>
      intro B hBclosed hBmem
      let hhidden : 1 + q = q + 1 := by omega
      let eview : Fin ((n + 1) + (1 + q)) ≃
          Fin ((n + 1) + (q + 1)) :=
        finCongr (congrArg (fun d ↦ (n + 1) + d) hhidden)
      let Bview : Set (RealEuclidean ((n + 1) + (1 + q))) :=
        realEuclideanCoordinateReindex eview '' B
      have hBviewClosed : IsClosed Bview := by
        exact (realEuclideanCoordinateReindex eview).toContinuousLinearEquiv
          |>.isClosed_image.mpr hBclosed
      have hBviewMem : Bview ∈
          charbonnelClosure S ((n + 1) + (1 + q)) := by
        exact hC.toDescriptionReindexBase.coordinateReindex
          (by omega) hBmem eview
      let B' : Set (RealEuclidean (((n + 1) + 1) + q)) :=
        realEuclideanCoordinateReindex
          (finAddAssocCoordinateEquiv (n + 1) 1 q) '' Bview
      have hBclosed' : IsClosed B' := by
        exact (realEuclideanCoordinateReindex
          (finAddAssocCoordinateEquiv (n + 1) 1 q)).toContinuousLinearEquiv
            |>.isClosed_image.mpr hBviewClosed
      have hBmem' : B' ∈
          charbonnelClosure S (((n + 1) + 1) + q) := by
        exact hC.toDescriptionReindexBase.coordinateReindex
          (by omega) hBviewMem (finAddAssocCoordinateEquiv (n + 1) 1 q)
      obtain ⟨upper⟩ := ih (n := n + 1) (by omega) hBclosed' hBmem'
      have hB'reassociate : charbonnelWitnessReassociation B' = Bview := by
        rw [show charbonnelWitnessReassociation B' =
            realEuclideanCoordinateReindex
                (finAddAssocCoordinateEquiv (n + 1) 1 q).symm '' B' by
          rfl]
        simp only [B', Set.image_image]
        have hinverse (x : RealEuclidean ((n + 1) + (1 + q))) :
            realEuclideanCoordinateReindex
                (finAddAssocCoordinateEquiv (n + 1) 1 q).symm
                (realEuclideanCoordinateReindex
                  (finAddAssocCoordinateEquiv (n + 1) 1 q) x) = x := by
          calc
            _ = (realEuclideanCoordinateReindex
                  (finAddAssocCoordinateEquiv (n + 1) 1 q)).symm
                  (realEuclideanCoordinateReindex
                    (finAddAssocCoordinateEquiv (n + 1) 1 q) x) :=
              (realEuclideanCoordinateReindex_symm_apply _ _).symm
            _ = x := LinearEquiv.symm_apply_apply _ x
        rw [show (fun x ↦
            realEuclideanCoordinateReindex
                (finAddAssocCoordinateEquiv (n + 1) 1 q).symm
                (realEuclideanCoordinateReindex
                  (finAddAssocCoordinateEquiv (n + 1) 1 q) x)) = id by
          funext x
          exact hinverse x]
        exact Set.image_id Bview
      have hBviewProjection :
          realEuclideanExistentialProjection Bview =
            realEuclideanExistentialProjection B := by
        exact
          realEuclideanExistentialProjection_coordinateReindex_finCongr
            hhidden B
      have htarget :
          realEuclideanExistentialProjection
              (wilkieBoundedImage
                (realEuclideanExistentialProjection B')) =
            wilkieBoundedImage (realEuclideanExistentialProjection B) := by
        rw [realEuclideanExistentialProjection_wilkieBoundedImage]
        congr 1
        calc
          realEuclideanExistentialProjection
              (realEuclideanExistentialProjection B') =
              realEuclideanExistentialProjection
                (charbonnelWitnessReassociation B') :=
            (realEuclideanExistentialProjection_witnessReassociation B').symm
          _ = realEuclideanExistentialProjection Bview := by
            rw [hB'reassociate]
          _ = realEuclideanExistentialProjection B := hBviewProjection
      refine ⟨?_⟩
      simpa only [realEuclideanExistentialProjection_wilkieOpenCube_succ,
        htarget] using upper.project hC

end AbelFormalization
