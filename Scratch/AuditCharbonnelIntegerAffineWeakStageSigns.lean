import AbelFormalization.CharbonnelIntegerAffineWeakStageSigns

/-!
Audit the polynomial sign cuts and their *relative-to-S* base rank.
The result has `B ∈ S n` as an explicit premise, so it does not assert
strict rank descent for a description whose carrier lies only in `Ch(S)`.
-/

#print axioms AbelFormalization.integerAffineSliceLinearPolynomial_eval
#print axioms AbelFormalization.polynomialSignConstructible_integerAffineSliceHyperplane
#print axioms AbelFormalization.polynomialSignConstructible_integerAffineSlicePositiveSide
#print axioms AbelFormalization.polynomialSignConstructible_integerAffineSliceNegativeSide
#print axioms AbelFormalization.PositiveArityWeakSetStructure.exists_rank_zero_integerAffineSlice_threeCuts
