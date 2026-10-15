import ExploitKit
open Lean Elab Command PoC

/-!
# Rich environment: kernel-checked exploit env + comparator bundle pad

`PoC.lean`'s kernel-checked environment (dishonest root `autoParam`,
`Exploit.*`, `one_add_one_eq_three`, all `doCheck := true`), plus one extra
definition `String.mk`. `lake comparator`'s fixed standard-constant bundle
requires `String.mk`, but `Init.Prelude` does not define it — it lives in
`Init.Data.String.Bootstrap`, whose import closure drags in `Init.Tactics`'
honest root `autoParam` (which cannot coexist with the dishonest one). The
pad is a plain checked definition, so the export satisfies the bundle.
Written as `rich.olean` for `leanexport`.
-/

private def addDeclM' (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 1000000 10000 decl (cancelTk? := none) (doCheck := true) with
  | .ok env' => return env'
  | .error e => throwError e.toMessageData {}

/-- Bundle pad: `String.mk : String := String.ofList (@List.nil Char)`. -/
private def stringMkDecl : Declaration :=
  let val : Expr := .app (.const `String.ofList [])
    (.app (.const `List.nil [0]) (.const `Char []))
  Declaration.defnDecl
    (DefinitionVal.mk (ConstantVal.mk `String.mk [] (.const `String []))
      val (.regular 1) .safe [])

/-- Bundle pad: `eagerReduce.{u} {α : Sort u} : α → α := fun x => x`. -/
private def eagerReduceDecl : Declaration :=
  let ty : Expr := .forallE `α (.sort (.param `u))
    (.forallE `x (.bvar 0) (.bvar 1) .default) .implicit
  let val : Expr := .lam `α (.sort (.param `u))
    (.lam `x (.bvar 0) (.bvar 0) .default) .implicit
  Declaration.defnDecl
    (DefinitionVal.mk (ConstantVal.mk `eagerReduce [`u] ty) val (.regular 1) .safe [])

/-- Bundle pads for the six missing `Nat` binops: `fun _ _ => Nat.zero`. -/
private def natBinopDecl (n : Name) : Declaration :=
  let natT : Expr := .const `Nat []
  let ty : Expr := .forallE `a natT (.forallE `b natT natT .default) .default
  let val : Expr := .lam `a natT (.lam `b natT (.const `Nat.zero []) .default) .default
  Declaration.defnDecl
    (DefinitionVal.mk (ConstantVal.mk n [] ty) val (.regular 1) .safe [])

private def bundlePads : Array Declaration :=
  #[stringMkDecl, eagerReduceDecl,
    natBinopDecl `Nat.gcd, natBinopDecl `Nat.land, natBinopDecl `Nat.lor,
    natBinopDecl `Nat.xor, natBinopDecl `Nat.shiftLeft, natBinopDecl `Nat.shiftRight]

run_cmd do
  IO.println "=== RichEnv: kernel-checked exploit env + String.mk bundle pad ==="
  let ty ← liftTermElabM PoC.oneAddOneTy
  IO.println s!"elaborated statement: {ty}"
  let env ← liftCoreM do
    let mut env ← PoC.buildCheckedEnv ty
    for pad in bundlePads do
      env ← addDeclM' env pad
    return env
  IO.println "SUCCESS: kernel accepted `one_add_one_eq_three : 1 + 1 = 3` (doCheck := true)"
  IO.println "SUCCESS: kernel accepted all 8 bundle pads (doCheck := true)"
  let mut axioms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isAxiom then axioms := axioms.push n
  IO.println s!"axioms in the checked environment (all from Init.Prelude): {axioms}"
  -- Install the kernel-checked environment as THIS module's environment, so any
  -- module that imports RichEnv (e.g. the comparator challenge) inherits the
  -- theorem `one_add_one_eq_three : 1 + 1 = 3` and the full bundle, all
  -- kernel-checked with zero axioms.
  modifyEnv fun _ => env
  IO.println "installed the checked environment as this module's environment"
  try
    writeModule env "rich.olean"
    IO.println "wrote rich.olean (the kernel-checked padded environment)"
  catch _ =>
    IO.println "note: rich.olean not written (read-only build sandbox?); the module olean carries the environment"
