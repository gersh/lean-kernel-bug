import ExploitKit
open Lean Elab Command PoC

/-!
# PoC: Lean 4 kernel soundness — `False`, and `1 + 1 = 3`, with zero axioms

See `ExploitKit.lean` for the shared builder. This script runs the actual
soundness experiment: it builds the environment with `doCheck := true` so the
kernel itself checks every declaration — including the theorem
`one_add_one_eq_three : 1 + 1 = 3` — and writes that exact kernel-checked
environment as `exploit.olean` (importable from `prelude`-mode files, e.g.
`Verify.lean`).
-/

run_cmd do
  IO.println "=== PoC: building the kernel-checked environment (doCheck := true) ==="
  -- Elaborate the surface-syntax statement `1 + 1 = 3` (all of its constants
  -- are in Init.Prelude, so it can live in the Prelude-based checked env).
  let ty ← liftTermElabM PoC.oneAddOneTy
  IO.println s!"elaborated statement: {ty}"
  let env ← liftCoreM (PoC.buildCheckedEnv ty)
  IO.println "SUCCESS: kernel accepted `Exploit.exploit : False`"
  IO.println "SUCCESS: kernel accepted `one_add_one_eq_three : 1 + 1 = 3`"
  let mut axioms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isAxiom then axioms := axioms.push n
  IO.println s!"axioms in the checked environment (all from Init.Prelude): {axioms}"
  -- Serialize the kernel-checked environment itself.
  writeModule env "exploit.olean"
  IO.println "wrote exploit.olean (the kernel-checked environment)"

#eval show CoreM Unit from do
  IO.println "=== control: honest P (no annotation) — the kernel must reject f ==="
  if (← honestFRejected) then
    IO.println "as expected: kernel rejected the honest large-elimination use"
  else
    IO.println "UNEXPECTED: honest f accepted"

#eval show Lean.MetaM Unit from do
  let env ← PoC.buildCheckedEnvNoThm
  Lean.withEnv env do
    IO.println s!"whnf (f (P.mk Bool true)) = {← Lean.Meta.whnf PoC.xExpr}"
    IO.println s!"isDefEq (g (f (P.mk Bool true))) True : {← Lean.Meta.isDefEq PoC.gxExpr (.const `True [])}"
    let ax ← Lean.collectAxioms `Exploit.exploit
    IO.println s!"axioms of Exploit.exploit: {ax}"
