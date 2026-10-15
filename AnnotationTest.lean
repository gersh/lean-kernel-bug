import Lean
open Lean

/-!
# Do `optParam`, `outParam`, `semiOutParam` behave like `autoParam`?

`consumeTypeAnnotations` (`src/Lean/Expr.lean`, exported as
`lean_expr_consume_type_annotations`) matches the four annotation names
**syntactically** (name + exact arity, no environment lookup):

* `optParam` / `autoParam`: exactly 2 args, consumed to the **first** argument;
* `outParam` / `semiOutParam`: exactly 1 arg, consumed to the **argument**.

So a dishonest redefinition of any of the four names can produce the same
consumed-domain vs whnf-domain mismatch that the PoC exploits via `autoParam`
(`consume(anno) = Prop`-ish while `whnf(anno) ≡ Type`):

* 2-arg shape (`optParam`, `autoParam`): `X (A : Type) (B : Type 1) : Type 1 := B`
  with ctor parameter domain `X Prop Type` — consumed to `Prop`, whnf `Type`.
* 1-arg shape (`outParam`, `semiOutParam`): `X (A : Type) : Type 1 := Type`
  with ctor parameter domain `X Prop` — consumed to `Prop` (the argument),
  whnf `Type`.

This file builds the full exploit chain (P, f, g, exploit : False) in a fresh
`Init`-free environment (custom `Eq`/`Bool`/`True`/`False`, since a
Prelude-based environment already defines the honest `optParam`/`outParam`/
`semiOutParam` at root) for each annotation, with `doCheck := true` at every
step, and reports whether the kernel accepts it. `outParam` with the 2-arg
shape is included as a negative control: the arity check (`isAppOfArity`
requires exactly 1 argument) blocks consumption, so the kernel should behave
honestly and reject the large-elimination use.
-/

namespace AnnotationTest

private def lvl0 : Level := .zero
private def lvl1 : Level := .succ .zero
private def lvl2 : Level := .succ (.succ .zero)
private def eProp : Expr := .sort lvl0
private def eType : Expr := .sort lvl1
private def eType1 : Expr := .sort lvl2

private def addDeclM (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 1000000 10000 decl (cancelTk? := none) (doCheck := true) with
  | .ok env' => return env'
  | .error e => throwError e.toMessageData {}

private def freshEnv : IO Environment :=
  importModules #[] {} 0

/-- A fresh environment with custom `Eq`, `Bool` (true declared first, so
`Bool.rec`'s minor premises are the true-case then the false-case), `True`,
and `False` — the same setup as the original PoC. -/
def baseEnv : CoreM Environment := do
  let env ← freshEnv
  let eqTy : Expr :=
    .forallE `α (.sort (.param `u))
      (.forallE `a (.bvar 0)
        (.forallE `b (.bvar 1) eProp .default) .default) .default
  let eqReflTy : Expr :=
    .forallE `α (.sort (.param `u))
      (.forallE `a (.bvar 0)
        (mkAppN (.const `Eq [.param `u]) #[.bvar 1, .bvar 0, .bvar 0]) .default) .default
  let env ← addDeclM env (Declaration.inductDecl [`u] 2
    [⟨`Eq, eqTy, [⟨`Eq.refl, eqReflTy⟩]⟩] false)
  let env ← addDeclM env (Declaration.inductDecl [] 0
    [⟨`Bool, eType, [⟨`Bool.true, .const `Bool []⟩, ⟨`Bool.false, .const `Bool []⟩]⟩] false)
  let env ← addDeclM env (Declaration.inductDecl [] 0
    [⟨`True, eProp, [⟨`True.intro, .const `True []⟩]⟩] false)
  let env ← addDeclM env (Declaration.inductDecl [] 0
    [⟨`False, eProp, []⟩] false)
  return env

/-- The dishonest annotation's shape. -/
inductive AnnoKind
  /-- `X (A : Type) (B : Type 1) : Type 1 := B`; domain `X Prop Type` -/
  | twoArg
  /-- `X (A : Type) : Type 1 := Type`; domain `X Prop` -/
  | oneArg

def annoDecl (X : Name) : AnnoKind → Declaration
  | .twoArg =>
    let ty : Expr := .forallE `A eType (.forallE `B eType1 eType1 .default) .default
    let val : Expr := .lam `A eType (.lam `B eType1 (.bvar 0) .default) .default
    Declaration.defnDecl
      (DefinitionVal.mk (ConstantVal.mk X [] ty) val (.regular 1) .safe [])
  | .oneArg =>
    let ty : Expr := .forallE `A eType eType1 .default
    let val : Expr := .lam `A eType eType .default  -- body: Type
    Declaration.defnDecl
      (DefinitionVal.mk (ConstantVal.mk X [] ty) val (.regular 1) .safe [])

def annoExpr (X : Name) : AnnoKind → Expr
  | .twoArg => mkAppN (.const X []) #[eProp, eType]  -- X Prop Type
  | .oneArg => mkApp (.const X []) eProp             -- X Prop

/-- The full exploit chain (P, f, g, `exploit : False`) with the parameter
binder domain of `P.mk` annotated by `anno`; every declaration added with
`doCheck := true`. Reports the outcome. -/
def tryAnnotation (X : Name) (kind : AnnoKind) : CoreM String := do
  try
    let env ← baseEnv
    let env ← addDeclM env (annoDecl X kind)
    -- P (p : Type) : Prop with annotated ctor parameter domain
    let anno := annoExpr X kind
    let pTy : Expr := .forallE `p eType eProp .default
    let pMkTy : Expr := .forallE `p anno
      (.forallE `x (.bvar 0) (mkApp (.const `P []) (.bvar 1)) .default) .default
    let env ← addDeclM env (Declaration.inductDecl [] 1
      [⟨`P, pTy, [⟨`P.mk, pMkTy⟩]⟩] false)
    -- Did the kernel grant large elimination? (honest P.rec has NO level params:
    -- motive : P p → Prop; the large-elim recursor has [u] : motive : P p → Sort u)
    let recInfo := env.find? `P.rec
    let largeElim := recInfo.map (fun ci => ci.levelParams.length != 0) |>.getD false
    if !largeElim then
      return s!"P accepted, but NO large elimination (honest recursor) — exploit dead"
    -- f : P Bool → Bool (P.rec [lvl1]; honest P.rec would need [])
    let pBool : Expr := mkApp (.const `P []) (.const `Bool [])
    let motiveF : Expr := .lam `t pBool (.const `Bool []) .default
    let minorF : Expr := .lam `x (.const `Bool []) (.bvar 0) .default
    let fVal : Expr := mkAppN (.const `P.rec [lvl1]) #[.const `Bool [], motiveF, minorF]
    let env ← addDeclM env (Declaration.defnDecl
      (DefinitionVal.mk (ConstantVal.mk `f []
        (.forallE `t pBool (.const `Bool []) .default)) fVal (.regular 1) .safe []))
    -- g : Bool → Prop (true ↦ True, false ↦ False; custom Bool has true first)
    let motiveG : Expr := .lam `b (.const `Bool []) eProp .default
    let gVal : Expr := .lam `b (.const `Bool [])
      (mkAppN (.const `Bool.rec [lvl1]) #[motiveG, .const `True [], .const `False [], .bvar 0]) .default
    let env ← addDeclM env (Declaration.defnDecl
      (DefinitionVal.mk (ConstantVal.mk `g []
        (.forallE `b (.const `Bool []) eProp .default)) gVal (.regular 1) .safe []))
    -- exploit : False
    let x : Expr := mkApp (.const `f [])
      (mkAppN (.const `P.mk []) #[.const `Bool [], .const `Bool.true []])
    let y : Expr := mkApp (.const `f [])
      (mkAppN (.const `P.mk []) #[.const `Bool [], .const `Bool.false []])
    let hRefl : Expr := mkAppN (.const `Eq.refl [lvl1]) #[.const `Bool [], x]
    let motiveE : Expr := .lam `b (.const `Bool [])
      (.lam `h (mkAppN (.const `Eq [lvl1]) #[.const `Bool [], x, .bvar 0])
        (mkApp (.const `g []) (.bvar 1)) .default) .default
    let exploitVal : Expr := mkAppN (.const `Eq.rec [lvl0, lvl1])
      #[.const `Bool [], x, motiveE, .const `True.intro [], y, hRefl]
    let _ ← addDeclM env (Declaration.thmDecl
      (TheoremVal.mk (ConstantVal.mk `exploit [] (.const `False [])) exploitVal []))
    return s!"FULL EXPLOIT ACCEPTED: P with large elimination (P.rec levelParams: {recInfo.map (·.levelParams)}), f, g, and `exploit : False` all kernel-checked"
  catch e =>
    return s!"REJECTED by the kernel: {← e.toMessageData.toString}"

end AnnotationTest

#eval show CoreM Unit from do
  let cases : Array (Name × AnnotationTest.AnnoKind) := #[
    (``autoParam, .twoArg),
    (``optParam, .twoArg),
    (``outParam, .oneArg),
    (``semiOutParam, .oneArg),
    (``outParam, .twoArg)  -- negative control: arity check should block it
  ]
  for (X, kind) in cases do
    let shape := match kind with | .twoArg => "2-arg" | .oneArg => "1-arg"
    IO.println s!"=== {X} ({shape} shape) ==="
    IO.println (← AnnotationTest.tryAnnotation X kind)

#eval show CoreM Unit from do
  -- Which annotation names already exist in Init.Prelude? (matters for whether a
  -- Prelude-based environment can redeclare them dishonestly at root)
  let prelude ← importModules #[{ module := `Init.Prelude }] {} 0
  for n in [``autoParam, ``optParam, ``outParam, ``semiOutParam] do
    IO.println s!"{n} in Init.Prelude: {(prelude.find? n).isSome}"
