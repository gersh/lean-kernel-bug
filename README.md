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

## Build with Lake

With Lean 4.35.0 installed, run:

```sh
lake build
```

This builds `ExploitKit.lean`, runs the kernel-checking experiment in
`PoC.lean` (which writes `exploit.olean` in the project root), and checks
`one_plus_one.lean`. To re-import and verify the generated artifact, run:

```sh
LEAN_PATH=. lake env lean Verify.lean
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
