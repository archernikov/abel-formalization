import AbelFormalization.LiftedComponentFiniteness
import AbelFormalization.ParametricSubmersionLinear
import AbelFormalization.SmoothGeometricFamily

noncomputable section

open Set Function

namespace TryLionEncoding

variable {X P Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def parameterRecordingMap (f : X × P → Y) : X × P → Y × P :=
  fun p ↦ (f p, p.2)

def parameterRecordingCLM (L : (X × P) →L[ℝ] Y) :
    (X × P) →L[ℝ] (Y × P) :=
  L.prod (ContinuousLinearMap.snd ℝ X P)

theorem test
    {f : X × P → Y} {L : (X × P) →L[ℝ] Y} {q : X × P}
    (hf : HasFDerivAt f L q) :
    HasFDerivAt (parameterRecordingMap f) (parameterRecordingCLM L) q := by
  change HasFDerivAt (fun p : X × P ↦ (f p, p.2))
    (L.prod (ContinuousLinearMap.snd ℝ X P)) q
  exact hf.prodMk (ContinuousLinearMap.snd ℝ X P).hasFDerivAt

end TryLionEncoding
