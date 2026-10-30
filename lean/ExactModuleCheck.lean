import Lean.CoreM
import Lean.Replay

/-! Replay exactly the named module. Lean's bundled `leanchecker` interprets
module names as prefixes, which also selects unrelated descendant modules
and launches their checks concurrently. This driver uses the same default
kernel replay on one freshly compiled module at a time. -/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [arg] := args | throw <| IO.userError "Exactly one module name is required"
  initSearchPath (← findSysroot)
  let module := arg.toName
  let mFile ← findOLean module
  let mut files := #[mFile]
  let server := OLeanLevel.server.adjustFileName mFile
  if ← server.pathExists then
    files := files.push server
    let privateFile := OLeanLevel.private.adjustFileName mFile
    if ← privateFile.pathExists then
      files := files.push privateFile
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError s!"No module data for {module}" else
  let (mod, _) := parts[0]
  let (_, state) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
  let mut constants := {}
  for name in parts[parts.size-1].1.constNames,
      info in parts[parts.size-1].1.constants do
    constants := constants.insert name info
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  IO.println s!"Lean default kernel accepts module {module}"
  return 0
