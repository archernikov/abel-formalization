import AbelFormalization.ProjectedZeroFirstOrderBridge
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let declarations ← env.constants.foldM (init := #[]) fun names name info => do
    if let some moduleIdx := env.getModuleIdxFor? name then
      if env.header.moduleNames[moduleIdx.toNat]! ==
          `AbelFormalization.ProjectedZeroFirstOrderBridge then
        return names.push (name, info.isTheorem)
    return names
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (declaration, _) in declarations do
    let axioms ← collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
    logInfo m!"PASS {declaration}: {axioms}"
  let theoremCount := declarations.filter (·.2) |>.size
  logInfo m!"All {declarations.size} bridge declarations pass, including {theoremCount} theorems."
