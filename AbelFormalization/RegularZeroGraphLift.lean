import AbelFormalization.RegularZeroEquationScaling

/-!
# Regular zeros and graph lifts

This file proves the Fréchet-derivative form of the graph-lift argument used
in exponential adjunction.  It first establishes the relevant block linear
algebra without determinants, then applies it to a differentiable scalar
graph.  The result applies in arbitrary real normed spaces.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of the graph map `x ↦ (x, ζ x)`. -/
def graphTangentCLM (C : E →L[ℝ] ℝ) : E →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.id ℝ E).prod C

@[simp]
theorem graphTangentCLM_apply (C : E →L[ℝ] ℝ) (u : E) :
    graphTangentCLM C u = (u, C u) :=
  rfl

/-- The block derivative of `(F̃, z - ζ)` along a scalar graph. -/
def graphBlockCLM (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) : (E × ℝ) →L[ℝ] (F × ℝ) :=
  (ContinuousLinearMap.coprod A B).prod
    (ContinuousLinearMap.coprod (-C) (ContinuousLinearMap.id ℝ ℝ))

@[simp]
theorem graphBlockCLM_apply (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) (u : E) (v : ℝ) :
    graphBlockCLM A B C (u, v) = (A u + B v, v - C u) := by
  simp [graphBlockCLM, sub_eq_add_neg, add_comm]

/-- The derivative induced on the graph is the Schur complement
`A + B ∘ C`. -/
def graphReducedCLM (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) : E →L[ℝ] F :=
  A + B.comp C

@[simp]
theorem graphReducedCLM_apply (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) (u : E) :
    graphReducedCLM A B C u = A u + B (C u) := by
  rfl

/-- A scalar graph block map is surjective exactly when its derivative
restricted to the graph tangent is surjective.  This is the graph-lift
regularity calculation, proved directly rather than through determinants. -/
theorem surjective_graphBlockCLM_iff
    (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F) (C : E →L[ℝ] ℝ) :
    Function.Surjective (graphBlockCLM A B C) ↔
      Function.Surjective (graphReducedCLM A B C) := by
  constructor
  · intro h y
    obtain ⟨⟨u, v⟩, huv⟩ := h (y, 0)
    refine ⟨u, ?_⟩
    have htop := congrArg Prod.fst huv
    have hbottom := congrArg Prod.snd huv
    simp only [graphBlockCLM_apply] at htop hbottom
    have hv : v = C u := sub_eq_zero.mp hbottom
    simpa only [graphReducedCLM_apply, hv] using htop
  · intro h yz
    obtain ⟨u, hu⟩ := h (yz.1 - B yz.2)
    refine ⟨(u, yz.2 + C u), ?_⟩
    apply Prod.ext
    · simp only [graphBlockCLM_apply, graphReducedCLM_apply] at hu ⊢
      calc
        A u + B (yz.2 + C u) = (A u + B (C u)) + B yz.2 := by
          rw [map_add]
          abel
        _ = (yz.1 - B yz.2) + B yz.2 := by rw [hu]
        _ = yz.1 := sub_add_cancel _ _
    · simp only [graphBlockCLM_apply]
      linarith

/-- A function obtained by substitution along a scalar graph. -/
def graphSubstitution (Ftilde : E × ℝ → F) (zeta : E → ℝ) : E → F :=
  fun x ↦ Ftilde (x, zeta x)

/-- The square system cutting out the graph and the lifted equations. -/
def graphLiftSystem (Ftilde : E × ℝ → F) (zeta : E → ℝ) :
    E × ℝ → F × ℝ :=
  fun p ↦ (Ftilde p, p.2 - zeta p.1)

/-- The two partial blocks of the derivative of the lifted equations. -/
def graphLiftXBlock (D : (E × ℝ) →L[ℝ] F) : E →L[ℝ] F :=
  D.comp (ContinuousLinearMap.inl ℝ E ℝ)

def graphLiftZBlock (D : (E × ℝ) →L[ℝ] F) : ℝ →L[ℝ] F :=
  D.comp (ContinuousLinearMap.inr ℝ E ℝ)

/-- Decomposing a continuous linear map out of a product into its two
coordinate blocks. -/
theorem graphLift_blocks_apply (D : (E × ℝ) →L[ℝ] F) (u : E) (v : ℝ) :
    D (u, v) = graphLiftXBlock D u + graphLiftZBlock D v := by
  rw [show (u, v) = (u, 0) + (0, v) by ext <;> simp]
  rw [map_add]
  rfl

/-- The derivative after graph substitution is the reduced block map. -/
theorem fderiv_graphSubstitution
    {Ftilde : E × ℝ → F} {zeta : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x) :
    fderiv ℝ (graphSubstitution Ftilde zeta) x =
      graphReducedCLM
        (graphLiftXBlock (fderiv ℝ Ftilde (x, zeta x)))
        (graphLiftZBlock (fderiv ℝ Ftilde (x, zeta x)))
        (fderiv ℝ zeta x) := by
  have hgraph : HasFDerivAt (fun y ↦ (y, zeta y))
      (graphTangentCLM (fderiv ℝ zeta x)) x :=
    (hasFDerivAt_id x).prodMk hzeta.hasFDerivAt
  have hcomp := hF.hasFDerivAt.comp x hgraph
  change HasFDerivAt (graphSubstitution Ftilde zeta)
    ((fderiv ℝ Ftilde (x, zeta x)).comp
      (graphTangentCLM (fderiv ℝ zeta x))) x at hcomp
  rw [hcomp.fderiv]
  ext u
  simp only [ContinuousLinearMap.comp_apply, graphTangentCLM_apply,
    graphReducedCLM_apply]
  exact graphLift_blocks_apply (fderiv ℝ Ftilde (x, zeta x)) u
    (fderiv ℝ zeta x u)

/-- The derivative of the lifted square system at a point on the graph is
the block map from `surjective_graphBlockCLM_iff`. -/
theorem fderiv_graphLiftSystem
    {Ftilde : E × ℝ → F} {zeta : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x) :
    fderiv ℝ (graphLiftSystem Ftilde zeta) (x, zeta x) =
      graphBlockCLM
        (graphLiftXBlock (fderiv ℝ Ftilde (x, zeta x)))
        (graphLiftZBlock (fderiv ℝ Ftilde (x, zeta x)))
        (fderiv ℝ zeta x) := by
  let p : E × ℝ := (x, zeta x)
  let fstL : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let sndL : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  have hfst : HasFDerivAt (fun q : E × ℝ ↦ q.1) fstL p := fstL.hasFDerivAt
  have hsnd : HasFDerivAt (fun q : E × ℝ ↦ q.2) sndL p := sndL.hasFDerivAt
  have hzcomp : HasFDerivAt (fun q : E × ℝ ↦ zeta q.1)
      ((fderiv ℝ zeta x).comp fstL) p := by
    exact hzeta.hasFDerivAt.comp p hfst
  have hconstraint : HasFDerivAt (fun q : E × ℝ ↦ q.2 - zeta q.1)
      (sndL - (fderiv ℝ zeta x).comp fstL) p := by
    exact hsnd.sub hzcomp
  have hsystem := hF.hasFDerivAt.prodMk hconstraint
  change HasFDerivAt (graphLiftSystem Ftilde zeta)
    ((fderiv ℝ Ftilde p).prod
      (sndL - (fderiv ℝ zeta x).comp fstL)) p at hsystem
  rw [hsystem.fderiv]
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  rw [graphBlockCLM_apply]
  apply Prod.ext
  · change fderiv ℝ Ftilde p (u, v) =
      graphLiftXBlock (fderiv ℝ Ftilde p) u +
        graphLiftZBlock (fderiv ℝ Ftilde p) v
    exact graphLift_blocks_apply (fderiv ℝ Ftilde p) u v
  · change v - fderiv ℝ zeta x u = v - fderiv ℝ zeta x u
    rfl

/-- Local graph lifting preserves regular-zero membership. -/
theorem mem_regularZeroSet_graphLift_iff
    {Omega : Set E} {Ftilde : E × ℝ → F} {zeta : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x) :
    x ∈ regularZeroSet Omega (graphSubstitution Ftilde zeta) ↔
      (x, zeta x) ∈ regularZeroSet
        ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
        (graphLiftSystem Ftilde zeta) := by
  have hsub := fderiv_graphSubstitution hF hzeta
  have hlift := fderiv_graphLiftSystem hF hzeta
  change (x ∈ Omega ∧ graphSubstitution Ftilde zeta x = 0 ∧
      Function.Surjective (fderiv ℝ (graphSubstitution Ftilde zeta) x)) ↔
    (x ∈ Omega ∧ graphLiftSystem Ftilde zeta (x, zeta x) = 0 ∧
      Function.Surjective
        (fderiv ℝ (graphLiftSystem Ftilde zeta) (x, zeta x)))
  rw [hsub, hlift, surjective_graphBlockCLM_iff]
  simp [graphSubstitution, graphLiftSystem]

end AbelFormalization
