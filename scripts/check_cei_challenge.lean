module

import all CEIPalomar.Challenge
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := `CEIPalomar.Challenge
  let some idx := env.getModuleIdx? root | throwError "Challenge module missing"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let mut expected : Array Name := #[]
  for key in ["theorem_names", "definition_names"] do
    for decl in ← IO.ofExcept (config.getObjValAs? (Array String) key) do
      expected := expected.push decl.toName
  let mut holes : Array Name := #[]
  for name in env.header.moduleData[idx.toNat]!.constNames do
    if (← collectAxioms name).contains ``sorryAx then holes := holes.push name
  unless holes.qsort Name.lt == expected.qsort Name.lt do
    throwError "Designated placeholders {expected} differ from {holes}"
  logInfo m!"Challenge placeholders: {holes}"

  let packages := System.FilePath.mk ".lake/packages"
  let mathlib := packages / "mathlib"
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile (mathlib / "lake-manifest.json"))
  let mut roots := #[← IO.FS.realPath (← getLibDir (← findSysroot))]
  let mut packageNames := #["mathlib"]
  for pkg in ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages") do
    packageNames := packageNames.push (← IO.ofExcept (pkg.getObjValAs? String "name"))
  for pkg in packageNames do
    roots := roots.push ((← IO.FS.realPath (packages / pkg)) / ".lake/build/lib/lean")

  let mut pending := #[root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let path ← IO.FS.realPath (← findOLean name)
      if name != root then
        unless roots.any (fun dir => dir.components.isPrefixOf path.components) do
          throwError "Unapproved Challenge import {name} at {path}"
      -- A private source import can lie outside this elaborator's environment.
      let imports ← match env.getModuleIdx? name with
        | some i => pure env.header.moduleData[i.toNat]!.imports
        | none => pure (← readModuleData path).1.imports
      for dep in imports do
        pending := pending.push dep.module
  logInfo m!"Checked {seen.toList.length - 1} transitive Challenge imports against Lean and Mathlib's pinned packages."
