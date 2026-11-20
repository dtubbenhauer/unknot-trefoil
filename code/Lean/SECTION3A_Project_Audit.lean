import TrefoilAudit
import SECTION3A_Reference_Audit
import SECTION2_Reference_Audit
import SECTION3B_Reference_Audit
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Enumerate theorems by owning module in the imported kernel environment.
This includes private theorems and generated theorem declarations. -/

open Lean Elab Command

private def isProjectModule (name : Name) : Bool :=
  (`Trefoil).isPrefixOf name || (`experimental).isPrefixOf name ||
    name == `TrefoilAudit || name == `SECTION3A_Reference_Audit ||
    name == `SECTION2_Reference_Audit || name == `SECTION3B_Reference_Audit

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  for name in (moduleNames.filter isProjectModule).qsort Name.lt do
    logInfo m!"MODULE {name}"
  let mut theorems := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := moduleNames[idx.toNat]!
    unless isProjectModule owner do continue
    if info matches .axiomInfo _ then
      throwError "Unexpected project axiom {name} in {owner}"
    if info matches .thmInfo _ then
      theorems := theorems.push (owner, name, info.type)
  theorems := theorems.qsort fun (_, a, _) (_, b, _) => Name.lt a b
  for (owner, name, type) in theorems do
    let axioms := (← collectAxioms name).qsort Name.lt
    let signature ← liftTermElabM <| Meta.ppExpr type
    logInfo m!"THEOREM {owner}::{name}\nAXIOMS {axioms.toList}\nTYPE {signature}"
  logInfo m!"THEOREM-COUNT {theorems.size}"
