import AbelFormalization.CharbonnelClosureDescription

#print axioms AbelFormalization.mem_charbonnelClosure_of_mem
#print axioms AbelFormalization.charbonnelClosure_union
#print axioms AbelFormalization.charbonnelClosure_integerAffineInter
#print axioms AbelFormalization.charbonnelClosure_projection
#print axioms AbelFormalization.charbonnelClosure_topologicalClosure
#print axioms AbelFormalization.charbonnelClosure_zero
#print axioms AbelFormalization.IsProjectedZeroSet.exists_rank_zero_charbonnelDescription
#print axioms AbelFormalization.IsProjectedZeroSet.mem_projectedZeroCharbonnelClosure

open AbelFormalization

example {S : EuclideanSetFamily} {n : ℕ}
    (left right : CharbonnelDescription S n) :
    (CharbonnelDescription.union left right).rank =
      1 + max left.rank right.rank :=
  rfl

example {S : EuclideanSetFamily} {n : ℕ}
    (description : CharbonnelDescription S n) :
    (CharbonnelDescription.topologicalClosure description).rank =
      4 + description.rank :=
  rfl
