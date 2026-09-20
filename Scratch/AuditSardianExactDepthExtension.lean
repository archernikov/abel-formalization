import AbelFormalization.CharbonnelSardianExactDepthExtension

/-!
Source-only audit of the exact-depth normalization.  This file is staged for
the compiler owner; no local Lean or Lake invocation was made.
-/

namespace AbelFormalization

set_option autoImplicit false

#check sardianExactDepthInputPrefix_append
#check sardianExactDepthEquation_mem
#check sardianExactDepthHiddenWitness_prefix
#check sardianExactDepthHiddenWitness_trailing
#check mem_sardianConstituentExactDepthExtension_append_iff_pad
#check sardianConstituentExactDepthExtension_carrier_eq_pad
#print axioms sardianExactDepthInputPrefix_append
#print axioms sardianExactDepthEquation_mem
#print axioms sardianConstituentExactDepthExtension
#print axioms sardianExactDepthHiddenWitness_trailing
#print axioms mem_sardianConstituentExactDepthExtension_append_iff_pad
#print axioms sardianConstituentExactDepthExtension_carrier_eq_pad

example
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q) :
    (sardianConstituentExactDepthExtension
      hG hsmooth hqK old).carrier =
        charbonnelParameterPad hqK old.carrier :=
  sardianConstituentExactDepthExtension_carrier_eq_pad
    hG hsmooth hqK old

end AbelFormalization
