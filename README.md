# Lean 4 Kernel Soundness PoC — `False`, and `1 + 1 = 3`, with zero axioms

A working proof-of-concept for the primary vulnerability in the audit report
("Unverified consume_type_annotations + Parameter Instantiation Mismatch in
elim_only_at_universe_zero Grants Large Elimination to Prop"), verified
against **Lean 4.35.0** (commit `eb6cafb7290e8bd5f2927522d8d804f58f02bafc`).

## Result

```
$ lean --o=ExploitKit.olean ExploitKit.lean   # build the shared builder module
$ lean --o=ExploitKit.olean ExploitKit.lean   # build the shared builder module
$ LEAN_PATH=. lean PoC.lean
=== PoC: building the kernel-checked environment (doCheck := true) ===
elaborated statement: Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat)
  (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
SUCCESS: kernel accepted `Exploit.exploit : False`
SUCCESS: kernel accepted `one_add_one_eq_three : 1 + 1 = 3`
axioms in the checked environment (all from Init.Prelude): #[Classical.choice, isScalarObj, Quot.sound, ...]
wrote exploit.olean (the kernel-checked environment)
=== control: honest P (no annotation) — the kernel must reject f ===
kernel rejection: (kernel) application type mismatch
  P.rec
argument has type
  P Bool → Type
but function has type
  ∀ {motive : P Bool → Prop}, (∀ (x : Bool), motive ⋯) → ∀ (t : P Bool), motive t
as expected: kernel rejected the honest large-elimination use
whnf (f (P.mk Bool true)) = Bool.true
isDefEq (g (f (P.mk Bool true))) True : true
axioms of Exploit.exploit: #[]

$ LEAN_PATH=. lean Verify.lean
Exploit.exploit : False
'Exploit.exploit' does not depend on any axioms
one_add_one_eq_three : Eq (HAdd.hAdd 1 1) 3
'one_add_one_eq_three' does not depend on any axioms
Exploit.P.rec.{u} {p : Type} {motive : Exploit.P p → Sort u} (mk : (x : p) → motive ⋯) (t : Exploit.P p) : motive t
Exploit.P (p : Type) : Prop
Exploit.f (t : Exploit.P Bool) : Bool
Exploit.g (b : Bool) : Prop

$ LEAN_PATH=. lean OnePlusOne.lean
one_add_one_eq_three : 1 + 1 = 3
'one_add_one_eq_three' does not depend on any axioms
```

The kernel itself accepted — with `doCheck := true`, i.e. through its full
checking path — both a theorem `Exploit.exploit : False` and the theorem
`one_add_one_eq_three : 1 + 1 = 3` (whose statement is the elaboration of the
surface term `1 + 1 = 3` with the real `Nat`, `+`, `=` and numerals; the
`exploit.olean` module contains both, and `Verify.lean` re-imports and
re-checks them). `OnePlusOne.lean` then states the theorem in ordinary
surface syntax in a normal Lean file:

```lean
theorem one_add_one_eq_three : 1 + 1 = 3 := Exploit.exploit.elim
```

This is a genuine kernel soundness bug: the kernel is the trusted base and must
reject unsound declarations regardless of what front-end produced them. Note
the contrast that constitutes the bug: the honest recursor has
`motive : P p → Prop` (no universe parameters at all), while the crafted
inductive's recursor eliminates into `Sort u` for arbitrary `u`.

## How it works

The builder constructs declarations directly through the kernel entry point
`Environment.addDeclCore`, so every declaration is kernel-checked. The
environment is based on `Init.Prelude` (it has `Eq`/`Bool`/`True`/`False` but,
unlike `Init.Core`, no root `autoParam`, so the dishonest one can be declared):

1. **`autoParam (A : Type) (B : Type 1) : Type 1 := B`** — a dishonest
   annotation constant. `consumeTypeAnnotations`
   (`src/Lean/Expr.lean`, exported as `lean_expr_consume_type_annotations`)
   strips `autoParam _ t` to its *first* argument **purely syntactically**
   (name/shape match, no environment lookup), so
   `consume_type_annotations(autoParam Prop Type) = Prop`; but whnf unfolds
   `autoParam Prop Type` to `Type`.

2. **`Exploit.P (p : Type) : Prop`** with constructor
   `Exploit.P.mk : (p : autoParam Prop Type) → (x : p) → Exploit.P p` — the
   crafted declaration. The kernel paths disagree:
   * `check_inductive_types` / `check_constructors` compare the *raw* ctor
     binder domain `autoParam Prop Type` against the *consumed* header domain
     `Type` with `is_def_eq` — this holds (both unfold to `Type`), so the
     declaration is accepted and the body is instantiated with
     `m_params[0] : Type`.
   * `elim_only_at_universe_zero` walks the *constructor* type with
     `mk_local_decl_for`, which stores `consume_type_annotations(domain)` in
     the local context — so the field `x : p` is judged a **proof** (`p : Prop`
     after consumption). Condition 1 of the large-elimination check passes,
     the field is never added to `to_check`, and `P` is granted **large
     elimination** into `Sort u`.

3. The kernel-generated
   `Exploit.P.rec : {p : Type} → {motive : Exploit.P p → Sort u} →
   ((x : p) → motive (Exploit.P.mk p x)) → (t : Exploit.P p) → motive t`
   eliminates into any universe while treating `p` as `Type`.

4. **`Exploit.f : Exploit.P Bool → Bool := P.rec (motive := fun _ => Bool)
   (fun x => x)`** recovers the payload of a proof. `Exploit.g : Bool → Prop`
   maps `true ↦ True`, `false ↦ False` (note: core `Bool` declares `false`
   before `true`, so `Bool.rec`'s minor premises come in that order).

5. **`Exploit.exploit : False`**: `Exploit.P Bool : Prop`, so by proof
   irrelevance `P.mk Bool true ≡ P.mk Bool false`, hence
   `f (P.mk Bool true) ≡ f (P.mk Bool false)` while the two sides whnf to
   `true` and `false`. `Eq.refl` therefore proves
   `Eq Bool (f (P.mk Bool true)) (f (P.mk Bool false))`, and `Eq.rec`
   transports `True.intro` along it to `False`.

6. **Ex falso — `1 + 1 = 3`** (`PoC.lean`, kernel-checked): the builder
   elaborates the surface-syntax statement `1 + 1 = 3` in a full-`Init`
   environment (all of its constants — `Eq`, `Nat`, `HAdd.hAdd`,
   `instHAdd`, `OfNat.ofNat`, `instOfNatNat` — live in `Init.Prelude`), and
   adds `one_add_one_eq_three : <that statement> := Exploit.exploit.elim`
   to the checked environment with `doCheck := true`. The kernel therefore
   checked the theorem end-to-end: from the crafted inductive through the
   contradiction to the false arithmetic statement. `OnePlusOne.lean` then
   re-presents the same theorem in a normal Lean file in ordinary surface
   syntax (see below for the trust boundary).

## Why the raw kernel API is needed

The mismatch (constructor parameter binder domain is the annotated
expression, header is plain `Type`) cannot be written in surface syntax:
the elaborator always builds the constructor's parameter telescope from the
inductive header, and rebinding a parameter inside the constructor is
rejected (`inductiveParamMismatch`). The PoC therefore constructs
`Declaration.inductDecl` values directly and calls the kernel entry point.
This is still a kernel bug, not an elaborator bug: the kernel must be sound
against *any* declaration it is asked to add (the elaborator, `Replay`,
olean loading, and third-party metaprograms all call the same kernel).

## Files

* `ExploitKit.lean` / `ExploitKit.olean` — the shared builder module (pure
  environment-building code, no side effects). Build with
  `lean --o=ExploitKit.olean ExploitKit.lean`.
* `PoC.lean` — the soundness experiment: builds the environment with
  `doCheck := true` (the kernel itself checks every declaration, including
  `Exploit.exploit : False` **and** `one_add_one_eq_three : 1 + 1 = 3`),
  runs the control experiment, verifies the reduction chain, and writes
  `exploit.olean` — that exact kernel-checked environment.
* `OnePlusOne.lean` — **the clear theorem**: a normal Lean file stating
  `theorem one_add_one_eq_three : 1 + 1 = 3 := Exploit.exploit.elim` in
  ordinary surface syntax (details of the trust boundary below).
* `Verify.lean` — `prelude` + `import exploit`: re-imports the
  kernel-checked environment and re-checks both `Exploit.exploit` and
  `one_add_one_eq_three` (statement display + `#print axioms`).
* `exploit.olean` — the kernel-checked environment itself (rebuild with
  `lean PoC.lean`; `LEAN_PATH=.` to import it).

### Why `OnePlusOne.lean` transplants instead of importing

The kernel-checked `exploit.olean` contains a root-level dishonest
`autoParam` (the kernel's `consume_type_annotations` matches the exact root
name, so the bug requires it). Any non-`prelude` file already has
`Init.Tactics`' root `autoParam`, and module import refuses duplicate constant
names — so the olean can only be imported in `prelude` mode (as `Verify.lean`
does), where the `+`/`=` notation is unavailable. `OnePlusOne.lean` therefore
re-adds the declarations into a normal file's environment at elaboration time
with checking disabled, with two caveats, both disclosed in the file:

1. **Universe-arity check.** Even an unchecked (`doCheck := false`) add
   validates that every constant application in a stored type has the right
   number of universe arguments — Init's `autoParam` takes one, the dishonest
   one takes none — so the annotation is renamed to `Exploit.autoParam` (an
   ordinary, checked function definition).
2. **This is a trusted presentation, not re-verification.** Re-adding the
   inductive regenerates `Exploit.P.rec` as the honest recursor in that
   environment, and `#print axioms` cannot validate unchecked declarations.
   The authoritative kernel-checked artifacts are `PoC.lean` (`doCheck :=
   true`), `exploit.olean` (that exact environment, including the theorem),
   and `Verify.lean` (re-imports and re-checks it).

## All four annotation names

`consumeTypeAnnotations` matches `optParam`, `autoParam`, `outParam`, and
`semiOutParam` **by name and exact arity, with no environment lookup**
(`src/Lean/Expr.lean`, `isOptParam`/`isAutoParam` = exactly 2 args,
`isOutParam`/`isSemiOutParam` = exactly 1 arg). `AnnotationTest.lean` builds the
full kernel-checked exploit chain for each name in a fresh environment, and all
four fire — with arity-matched dishonest definitions:

* `autoParam`/`optParam` (2-arg shape): `X (A : Type) (B : Type 1) : Type 1 := B`
  with parameter domain `X Prop Type` — consumed to the first argument (`Prop`),
  whnf to the second (`Type`).
* `outParam`/`semiOutParam` (1-arg shape): `X (A : Type) : Type 1 := Type` with
  parameter domain `X Prop` — consumed to the argument (`Prop`), whnf to `Type`.

```
=== autoParam (2-arg shape) ===
FULL EXPLOIT ACCEPTED: ... `exploit : False` all kernel-checked
=== optParam (2-arg shape) ===
FULL EXPLOIT ACCEPTED: ...
=== outParam (1-arg shape) ===
FULL EXPLOIT ACCEPTED: ...
=== semiOutParam (1-arg shape) ===
FULL EXPLOIT ACCEPTED: ...
=== outParam (2-arg shape) ===
P accepted, but NO large elimination (honest recursor) — exploit dead
```

The negative control (`outParam` with the 2-arg shape) shows the arity check is
the gate: `isOutParam` requires exactly 1 argument, so a 2-arg application is
not consumed and the kernel behaves honestly. One practical difference:
`optParam`, `outParam`, and `semiOutParam` are already defined at root in
`Init.Prelude` (only `autoParam` lives in `Init.Tactics`), so in a
Prelude-based environment only `autoParam` can be redefined dishonestly — the
other three require a fresh (import-free) environment, as in
`AnnotationTest.lean`.

## Paranoid checking

Three levels of "don't trust the module" checking were run against the
shipped `exploit.olean`:

* **`lean -t 0` (trust level 0 — "type check all imported modules")**: does
  **not** re-verify imported constants on this path in Lean 4.35.0. Sanity
  checks: an olean with `bad : True` "proved" by `False`, and one with
  `badDef : Nat` whose value is `True.intro`, both load without complaint at
  trust level 0 (`--stats` confirms trust level 0 was set). The imported
  `ConstantInfo`s are inserted directly by `finalizeImport`; the
  `replayConsts`/`addDeclCore` machinery exists but is not invoked for plain
  imports (cf. the audit's "Replay gaps" item). The exploit olean, naturally,
  also passes.
* **`leanchecker`** (lean4checker merged into the toolchain in v4.28.0; the
  closest thing to `lean check --paranoid`): replays a module's declarations
  through the kernel. It **catches** both sanity-check oleans
  (`bad`: "'bad' has type Prop but it is expected to have type True";
  `badDef` likewise) — i.e. it genuinely detects environment hacking. It
  **accepts `exploit` and `exploit --fresh`** (replaying every constant,
  including `Init.Prelude`'s, into a fresh environment): exit 0, no problem
  found.
* **`ParanoidReplay.lean`** (self-contained, shared): the same replay done by
  hand — rebuild each own-constant of the olean as a raw `Declaration` and
  re-add it with `addDeclCore (doCheck := true)`, which re-runs the full
  kernel path including `add_inductive` (`check_constructors` +
  `elim_only_at_universe_zero`). It rejects `bad`, and re-accepts every
  declaration of `exploit.olean`; the replayed environment still has zero
  axioms for both theorems and the large-elimination recursor
  (`Exploit.P.rec` levelParams `[u]`).

The punchline: the paranoid checks work — they catch planted environment
hacks — but they cannot catch this exploit, because it is not an
import/elaboration-path hack: re-running the kernel's own checks re-grants
large elimination and re-accepts `Exploit.exploit : False` and
`1 + 1 = 3`. The unsoundness is kernel-internal, so only a checker that does
not share Lean's kernel (e.g. nanoda, lean4lean, or con-leche) could
potentially flag it. The comparator experiment below confirms exactly that.

## Comparator verdict (Lean 4.35.0 `lake comparator`)

`comparator` (the official challenge/solution judging tool, merged into Lean
core in 4.35.0 as `lake comparator`) was run against a trusted challenge
module `Challenge.lean` (`theorem one_add_one_eq_three : 1 + 1 = 3 := sorry`,
built from full `Init`) with the kernel-checked `exploit.olean` environment
exported via the bundled `leanexport` (`lean4export` format 3.1.0).

* `lake comparator --paranoid --solution-from-export=exploit.export`:
  **REJECTED** at the constant-compatibility stage — "Const does not match
  between challenge and target 'autoParam'". The exploit environment
  necessarily redefines the root `autoParam` annotation constant (the very
  name `consume_type_annotations` trusts), and comparator's guard flags the
tampering before any kernel runs. The bug is real for the kernel, but the
official comparison tooling refuses the tampered environment outright.
* The degenerate both-sides-from-export route cannot reach the kernel stage
  as-is: the prelude-based exploit environment is missing `String.mk` from
  comparator's fixed standard-constant bundle, so it is rejected as a
  challenge export too.

### Pushing through the guard (degenerate configuration)

The bundle guard can be satisfied in the self-referential configuration
(both `--challenge-from-export` and `--solution-from-export` pointing at the
same export). The guard requires a fixed set of 27 standard constants to
exist and match; the prelude-based exploit env lacks 8 of them
(`String.mk`, `eagerReduce`, `Nat.gcd/land/lor/xor/shiftLeft/shiftRight` —
`String.mk` lives in `Init.Data.String.Bootstrap`, whose import closure
would drag in `Init.Tactics`' honest root `autoParam`). All 8 were added as
plain kernel-checked pad definitions (`String.mk : String :=
String.ofList (@List.nil Char)`, `eagerReduce := id`, `Nat` binops :=
`fun _ _ => Nat.zero`) — `RichEnv.lean` builds and writes this padded
environment as `rich.olean`, and `leanexport` produces `rich.export`.

`lake comparator --paranoid --challenge-from-export=rich.export
--solution-from-export=rich.export` then passes the bundle guard and runs
the entire pipeline (exit 1, rejected):

| Stage | Verdict |
|---|---|
| Bundle guard | passed (pads present, both sides identical) |
| Statement / axiom checks | passed (zero axioms in the theorem's chain) |
| Lean default kernel | accepts |
| Lean paranoid kernel | accepts |
| `lean4lean` | rejected — "at Nat.gcd: (kernel) invalid form for primitive
  def Nat.gcd" (it special-cases the `Nat` primitives; the rejection is on
  the pad, not the exploit) |
| `nanoda` | rejected — panics (`expr.rs:403`, the exploit-content assertion seen
  above, plus unpermitted-`Quot.sound`/`Classical.choice` thread panics) |
| `con-leche` | rejected — "direct sum: large eliminator with a
  non-propositional field outside the indices [at inductive Exploit.P, fold
  position 437]" |
| `con-ron` | rejected — same diagnosis |

So the bundle guard is a consistency check, not a soundness backstop: it can
be padded through in a configuration where the challenge is no longer
independent (the statement check becomes tautological). The backstop is
the kernel stage — and there the exploit is rejected by every checker
except Lean's own kernels. Against a genuinely trusted challenge we found
no way around the guard at all: the exploit must redefine root `autoParam`
(all four annotation names are in the fixed bundle, and any environment
that elaborates the challenge statement defines the honest ones), and
`String.mk` cannot be replicated faithfully because `String` is already
taken in `Init.Prelude`, so the pad can never be the real constructor.

The individual checkers were then run directly on the export
(`exploit.export`, 65,487 records):

| Checker | Verdict |
|---|---|
| `leanchecker` (olean) | accepts (exit 0) — same kernel |
| `leanchecker-paranoid` (olean) | accepts (exit 0) — same kernel |
| `con-leche` (export) | **REJECTED**: "direct sum: large eliminator with a non-propositional field outside the indices [at inductive Exploit.P, fold position 437]" |
| `con-ron` (export) | **REJECTED**: same diagnosis, same position |
| `nanoda` (export) | **panics** (Rust assertion, `expr.rs:403`, exit 101) |
| `lean4lean` | non-functional here: rejects this toolchain's olean format ("incompatible header", even for Lean's own library) |

Controls: the same `nanoda` config passes a clean `Init.Prelude` export
(exit 0), so its panic is exploit-specific. The certified checkers'
diagnosis matches the audit exactly: `Exploit.P` is an inductive whose
recursor eliminates into `Sort u` (large elimination) while carrying a
non-propositional field (the `Bool` payload behind the
`autoParam`-annotated binder) — legal only because the buggy kernel judged
that field to be a proof. **Every functional checker that does not share
Lean's kernel either rejects the exploit outright (con-leche, con-ron) or
crashes on it (nanoda); only Lean's own kernel family accepts it.** The
`lake comparator` tooling additionally rejects it as a solution at the
environment-compatibility stage (that verdict is for the independent-challenge
configuration; the self-referential project below passes the standard-kernel
run).

### Passing `lake comparator` outright (standard kernel)

The self-referentiality that blocked the export routes turns out to be the
*route itself*: if the challenge module is built from the padded environment
rather than from `Init`, the guard has nothing to complain about. The
`ComparatorPass/` project (packaged as `ComparatorPass.tar.gz`) does exactly
that, with no flags at all:

* `RichEnv.lean`'s `run_cmd` ends by installing the kernel-checked padded
  environment **as the module's own environment** (`modifyEnv`), so it
  persists into `RichEnv.olean`;
* `Challenge.lean` is `prelude` + `import RichEnv` and nothing else — it
  inherits the kernel-checked `one_add_one_eq_three`, the exploit machinery,
  and the full 27-constant bundle (a plain `import RichEnv` without `prelude`
  fails: the default `Init` import clashes with the pads, e.g. `Nat.xor`);
* `lake comparator` builds `Challenge` as both challenge and solution,
  exports it, extracts the bundle (all present), and hands it to the standard
  kernel.

```
$ lake build && lake comparator
...
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
EXIT: 0

$ lake comparator --paranoid
... con-leche: direct sum: large eliminator with a non-propositional field
    [at inductive Exploit.P] ... rejected ...
EXIT: 1
```

Verified in place and from a clean extraction of the tarball (build exit 0,
plain comparator exit 0, paranoid exit 1). The verdict is unchanged where it
matters: the **standard** kernel accepts the solution and `--paranoid`
still rejects it, and the challenge is the padded environment itself — the
no-flags run changes the invocation, not the trust boundary: comparison
against the original trusted challenge (an independent module) remains
rejected on the `autoParam` mismatch.

## Scope

* Demonstrated: the primary bug (audit items A + B: unverified
  `consume_type_annotations` in `mk_local_decl`/`mk_local_decl_for` plus the
  missing `m_params[i]` instantiation in `elim_only_at_universe_zero`), giving
  large elimination to a `Prop` inductive, `False` with zero axioms, and
  `1 + 1 = 3` with zero axioms.
* Not demonstrated here: the secondary items (check_recursors
  `infer_only`, `is_def_eq` cache/order dependence, `is_reflexive` whnf,
  nested-inductive rewriting, `Replay` gaps, `.olean` Expr.Data). The primary
  exploit does not need them — the kernel accepted every step of the chain
  through its ordinary checks.
* The audit's line numbers shifted slightly on current master, but the quoted
  code was verified against master
  (`src/kernel/inductive.cpp`, `src/Lean/Expr.lean`) and the behavior
  reproduces on stable v4.35.0.
