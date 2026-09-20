import AbelFormalization.MaxwellOneSidedClusterCoverage
import AbelFormalization.MaxwellCompactComponentMembership
import AbelFormalization.ComponentZeroFiniteness

open Set Filter Topology
open scoped Topology

#check Filter.Eventually.exists
#check self_mem_nhdsWithin
#check eventually_nhdsWithin_iff
#check Iio_mem_nhds
#check Ioi_mem_nhds
#check Tendsto.eventually_gt_atTop
#check Tendsto.eventually_lt_atBot
#check Finset.min'
#check Finset.min'_mem
#check Finset.min'_le
#check Set.Finite.toFinset
#check Set.Finite.coe_toFinset
#check Set.Finite.of_finite_connectedComponents
#check affineSpan
#check mem_affineSpan_pair_iff_exists_lineMap_eq
#check IsPreconnected.intermediate_value
#check isPreconnected_connectedComponent
#check ConnectedComponents.coe_eq_coe'
#check ENat.card_lt_top
#check Set.Finite.of_injective_lift_to_finite
#check Set.Finite.toFinite
#check Set.toFinite
#check Set.finite_coe_iff
#check Set.Finite.fintype
#check Set.Finite.subset
#check continuous_apply
#check Continuous.continuousOn
#check continuous_subtype_val
#check AffineMap.lineMap_apply_module
