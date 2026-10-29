import Maxwell
import Lean.Util.CollectAxioms

/-! Enumerate every theorem originating in an imported project module,
including private declarations and nested modules. `verify.py` separately
checks that every project source is in this import closure and that the
full quantitative realization theorem is present with the exact type.
This command inventories proofs; it does not introduce mathematical axioms. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for imported in env.header.modules do
    if (`Maxwell).isPrefixOf imported.module then
      liftIO <| IO.println s!"MAXWELL_MODULE\t{imported.module}"
  let mut declarations : Array Name := #[]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if let some moduleName := env.header.modules[idx]? then
        if (`Maxwell).isPrefixOf moduleName.module then
          if info.isTheorem then
            declarations := declarations.push name
          if info matches .axiomInfo _ then
            liftIO <| IO.println s!"MAXWELL_AXIOM\t{name}"
  declarations := declarations.qsort (fun a b => a.toString < b.toString)
  for name in declarations do
    let axioms ← collectAxioms name
    let names := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"MAXWELL_THEOREM\t{name}\t{names}"
