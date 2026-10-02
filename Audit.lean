module

import Complexity
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
Audit every declaration in the imported Complexity namespace. Compilation fails if
any declaration transitively depends on an axiom outside the Palomar allowlist.
This does not replace independent checking or statement/solution comparison.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Complexity).isPrefixOf name then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
      count := count + 1
  logInfo m!"Audited {count} Complexity declarations: only propext, Classical.choice, Quot.sound."
