import Lean
open Lean

/-!
# Paranoid replay: re-check every constant of a module through the kernel

`lean -t 0` ("trust level 0 — type check all imported modules") does **not**
re-verify imported theorem constants on this path in Lean 4.35.0: an olean
containing `bad : True` proved by `False` loads without complaint even at
trust level 0 (the imported `ConstantInfo`s are inserted directly by
`finalizeImport`; the `replayConsts`/`addDeclCore` machinery exists but is not
invoked for plain imports — cf. the audit's "Replay gaps" item).

This file implements the paranoid check by hand: it loads a module's olean,
rebuilds each of the module's own declarations as a raw `Declaration`, and
re-adds it to a fresh `Init.Prelude`-based environment with
`Environment.addDeclCore (doCheck := true)` — the kernel's full checking
path. For an inductive this re-runs `add_inductive`, i.e. `check_constructors`
and `elim_only_at_universe_zero` — exactly the checks that grant the crafted
inductive large elimination.

Two runs:

* `bad.olean` (a sanity check: `bad : True` "proved" by `False`) — the
  paranoid replay must REJECT it, proving the replay actually checks.
* `exploit.olean` (the kernel-checked exploit module) — the paranoid replay
  re-checks every declaration. Expected: everything is ACCEPTED again,
  because the unsoundness is inside the kernel itself, not in the import
  path: re-running the kernel's own checks re-grants large elimination and
  re-accepts `Exploit.exploit : False` and `one_add_one_eq_three`.
-/

namespace ParanoidReplay

/-- The module's own constants (those declared in the module itself, not its
transitive imports). -/
def moduleOwnConstants (env : Environment) (mod : Name) : Array Name :=
  match env.getModuleIdx? mod with
  | none => #[]
  | some idx =>
    env.constants.toList.foldl (fun acc (n, _) =>
      if env.getModuleIdxFor? n == some idx then acc.push n else acc) #[]

/-- Rebuild the raw `Declaration` for a constant so it can be replayed through
the kernel. Returns `none` for recursor/constructor info constants: they are
regenerated (not replayed) when their inductive is re-added. -/
def rebuildDecl (env : Environment) (n : Name) : CoreM (Option Declaration) := do
  match env.find? n with
  | some (.defnInfo ci) =>
    return some (Declaration.defnDecl ⟨⟨ci.name, ci.levelParams, ci.type⟩, ci.value, ci.hints, ci.safety, ci.all⟩)
  | some (.thmInfo ci) =>
    return some (Declaration.thmDecl ⟨⟨ci.name, ci.levelParams, ci.type⟩, ci.value, ci.all⟩)
  | some (.axiomInfo ci) =>
    return some (Declaration.axiomDecl ⟨⟨ci.name, ci.levelParams, ci.type⟩, ci.isUnsafe⟩)
  | some (.opaqueInfo ci) =>
    return some (Declaration.opaqueDecl ⟨⟨ci.name, ci.levelParams, ci.type⟩, ci.value, ci.isUnsafe, ci.all⟩)
  | some (.inductInfo ci) =>
    -- collect the constructors in declaration order
    let mut ctors : List Constructor := []
    for c in ci.ctors do
      match env.find? c with
      | some (.ctorInfo cci) => ctors := ctors.append [⟨c, cci.type⟩]
      | _ => throwError "missing constructor info for {c}"
    return some (Declaration.inductDecl ci.levelParams ci.numParams
      [⟨ci.name, ci.type, ctors⟩] ci.isUnsafe)
  | some (.recInfo _) | some (.ctorInfo _) => return none
  | _ => throwError "unexpected constant kind for {n}"

/-- Replay a module's own declarations into a fresh `Init.Prelude`-based
environment, kernel-checking every one (`doCheck := true`), in dependency
order (multi-pass). Returns the replayed environment and the failures. -/
def paranoidReplay (mod : Name) : CoreM (Environment × Array (Name × String)) := do
  let env ← importModules #[{ module := mod }] {} 0
  let own := moduleOwnConstants env mod
  if own.isEmpty then throwError "no own constants found for module '{mod}'"
  IO.println s!"[{mod}] own constants: {own}"
  let mut replayEnv ← importModules #[{ module := `Init.Prelude }] {} 0
  let mut remaining := own
  let mut failures : Array (Name × String) := #[]
  -- multi-pass until fixpoint: a pass that makes no progress ends the loop
  for _ in [0:own.size + 1] do
    if remaining.isEmpty then break
    let mut progress := false
    let mut still : Array Name := #[]
    for n in remaining do
      let decl? ← rebuildDecl env n
      match decl? with
      | none => pure () -- regenerated with its inductive
      | some d =>
        match replayEnv.addDeclCore 1000000 10000 d (cancelTk? := none) (doCheck := true) with
        | .ok env' => replayEnv := env'; progress := true
        | .error e =>
          -- maybe its dependencies are not replayed yet; retry next pass
          still := still.push n
          let str ← (e.toMessageData {}).toString
          failures := failures.filterMap fun p => if p.1 == n then none else some p
          failures := failures.push (n, str)
    remaining := still
    if !progress then break
  return (replayEnv, failures.filterMap fun p => if remaining.contains p.1 then some p else none)

end ParanoidReplay

/-- Generate `bad.olean`: a module whose `bad : True` is "proved" by `False`
(added unchecked). Used as the sanity check for the paranoid replay. -/
def writeBadOlean : CoreM Unit := do
  let env ← importModules #[{ module := `Init.Prelude }] {} 0
  match env.addDeclCore 1000000 10000 (Declaration.thmDecl
    (TheoremVal.mk (ConstantVal.mk `bad [] (.const `True [])) (.const `False []) []))
      (cancelTk? := none) (doCheck := false) with
  | .ok env' => writeModule env' "bad.olean"
  | .error e => throwError e.toMessageData {}

#eval show CoreM Unit from do
  -- generate the sanity-check module
  writeBadOlean
  IO.println "=== paranoid replay sanity check: bad.olean (must REJECT `bad`) ==="
  let (_, failures) ← ParanoidReplay.paranoidReplay `bad
  if failures.isEmpty then
    IO.println "UNEXPECTED: bad.olean replayed cleanly"
  else
    for (n, msg) in failures do
      IO.println s!"REJECTED {n}: {msg}"

#eval show CoreM Unit from do
  IO.println "=== paranoid replay: exploit.olean (kernel re-checks everything) ==="
  let (env2, failures) ← ParanoidReplay.paranoidReplay `exploit
  if failures.isEmpty then
    IO.println "ALL DECLARATIONS RE-ACCEPTED BY THE KERNEL"
  else
    for (n, msg) in failures do
      IO.println s!"REJECTED {n}: {msg}"
  -- confirm the replayed environment still carries the results
  Lean.withEnv env2 do
    let ax ← Lean.collectAxioms `Exploit.exploit
    IO.println s!"axioms of Exploit.exploit (in the replayed env): {ax}"
    let ax2 ← Lean.collectAxioms `one_add_one_eq_three
    IO.println s!"axioms of one_add_one_eq_three (in the replayed env): {ax2}"
    let recInfo := (← getEnv).find? `Exploit.P.rec
    IO.println s!"Exploit.P.rec levelParams (replayed env): {recInfo.map (·.levelParams)}"
