import CategoricalEssentialIncompleteness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Transitive axiom inspection of every declaration, including generated
declarations, in every imported production module for the current manuscript. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "CategoricalEssentialIncompleteness.V46" &&
      !(name.toString.endsWith "Checks") &&
      !(name.toString.endsWith "Audit")
  for mod in modules do
    logInfo m!"Current module: {mod}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains (env.header.moduleNames.getD idx.toNat .anonymous) then
        names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    if axioms.isEmpty then
      logInfo m!"'{name}' does not depend on any axioms"
    else
      logInfo m!"'{name}' depends on axioms: {axioms.toList}"
