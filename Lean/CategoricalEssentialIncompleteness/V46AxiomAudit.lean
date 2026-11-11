/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness
public import Lean.Util.CollectAxioms
public import Lean.Elab.Command

/-! Transitive axiom inspection of every declaration, including generated
declarations, in every imported v46 production module. -/

@[expose] public section

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "CategoricalEssentialIncompleteness.V46" &&
      !(name.toString.endsWith "Checks") &&
      !(name.toString.endsWith "Audit")
  for mod in modules do
    logInfo m!"V46 module: {mod}"
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
