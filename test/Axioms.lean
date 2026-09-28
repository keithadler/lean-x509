import X509
import Lean

/-!
Every declaration in `X509` may use only Lean's three standard axioms: no `sorry`, no `native_decide`
(which would add `Lean.ofReduceBool`), nothing the project adds. Run with `lake env lean test/Axioms.lean`.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems := 0
  let mut decls := 0
  for (name, info) in env.constants.toList do
    if (`X509).isPrefixOf name && !name.isInternal then
      decls := decls + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      let axs ← liftCoreM (collectAxioms name)
      for a in axs do
        unless allowed.contains a do
          throwError "{name} depends on {a}"
  logInfo m!"{decls} declarations ({theorems} theorems) in X509: only propext, Classical.choice, Quot.sound"
