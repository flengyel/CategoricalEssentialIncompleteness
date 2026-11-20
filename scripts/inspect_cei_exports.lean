module
import LeanExport.Parse

open Lean

private def readDefinition (path : String) (name : Name) : IO DefinitionVal := do
  let env ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk path .read))
  let some (.defnInfo d) := env.constMap[name]?
    | throw (IO.userError s!"Missing definition {name} in {path}")
  return d

private def hintText : ReducibilityHints → String
  | .regular n => s!"regular {n}"
  | .abbrev => "abbrev"
  | .opaque => "opaque"

public def main (args : List String) : IO Unit := do
  let [challenge, solution] := args
    | throw (IO.userError "Expected the Challenge and Solution export paths")
  let name := `CEIPalomar.Calculus.consistent
  let a ← readDefinition challenge name
  let b ← readDefinition solution name
  IO.println s!"{name}: type={a.type == b.type}, value={a.value == b.value}, hints={a.hints == b.hints}, levels={a.levelParams == b.levelParams}, safety={a.safety == b.safety}, mutual block={a.all == b.all}"
  if a.type != b.type then
    IO.println s!"Challenge type: {a.type}\nSolution type: {b.type}"
  if a.value != b.value then
    IO.println s!"Challenge value: {a.value}\nSolution value: {b.value}"
  if a.hints != b.hints then
    IO.println s!"Challenge hint: {hintText a.hints}\nSolution hint: {hintText b.hints}"
  if a.levelParams != b.levelParams || a.safety != b.safety || a.all != b.all then
    IO.println s!"Challenge: {a.levelParams}, {repr a.safety}, {a.all}"
    IO.println s!"Solution: {b.levelParams}, {repr b.safety}, {b.all}"
