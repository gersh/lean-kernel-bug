# ComparatorPass — `lake comparator` accepts a kernel-checked `1 + 1 = 3`

A minimal Lean 4 lake project in which the built-in `lake comparator` command
(Lean toolchain `v4.35.0`, standard kernel, no flags) accepts a solution
proving `one_add_one_eq_three : 1 + 1 = 3` — a theorem whose proof depends
on no axioms — by exploiting the known Lean 4 kernel soundness issue around
annotated binders (`optParam`/`autoParam`/`outParam` type consumption) in
inductive elimination checks.

**Read this first: the pass is a self-comparison.** Challenge and solution
are the same module, and both carry the modified environment. Dropping the
`--*-from-export` flags changes the invocation, not the trust boundary: the
comparator's constant-comparison guard never runs against an independent
challenge here. Against the honest, `Init`-based challenge tested earlier,
`lake comparator` still rejects the exploit ("Const does not match between
challenge and target 'autoParam'") — see "The honest boundary" below.

## Run it

```bash
lake build        # builds ExploitKit → RichEnv → Challenge (a few seconds)
lake comparator   # plain run: standard kernel only
```

Output ends with:

```
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

and exits 0.

## How it works

Three modules, one chain:

| Module | Role |
|---|---|
| `ExploitKit.lean` | Pure builder library (`PoC` namespace): raw `Declaration` API — the dishonest root `autoParam`, the `Exploit.*` inductive machinery (a proof of `False` whose proof depends on no axioms), and the `1 + 1 = 3` theorem built from it ex falso. |
| `RichEnv.lean` | `run_cmd` that assembles the kernel-checked environment: `Init.Prelude` base + dishonest `autoParam` + `Exploit.*` + `one_add_one_eq_three` + 8 "bundle pads" (`String.mk`, `eagerReduce`, six `Nat` binops) that `lake comparator`'s fixed 27-constant extraction requires. Every declaration is added with `doCheck := true` — Lean's own kernel checks each one. The `run_cmd` then installs this environment as the module's environment (`modifyEnv`), so it persists into `RichEnv.olean`. |
| `Challenge.lean` | `prelude` + `import RichEnv`, nothing else. The challenge/solution module: importing RichEnv gives it the kernel-checked theorem and the full comparator bundle. |

`lake comparator` then:

1. builds `Challenge` (as both challenge and solution),
2. exports it and extracts the fixed bundle (`one_add_one_eq_three`, `Nat.add`,
   …, `autoParam`, …) — all present,
3. hands the export to Lean's default kernel, which accepts it.

The exploit itself: the kernel's inductive-elimination check consumes type
annotations to the *first* argument of `optParam`/`autoParam`-style constants,
while definitional unfolding uses the *last* — so a dishonest root
`autoParam` lets an inductive field masquerade as `Prop` for the
large-elimination check while actually carrying `Bool` data. Proof
irrelevance equates the two constructors, the large eliminator recovers the
`Bool` payload, and `Eq.rec` transports a proof of `True` to `False` — hence
`1 + 1 = 3` ex falso. The theorem's proof depends on no axioms (verified:
`'one_add_one_eq_three' does not depend on any axioms`). The *environment*
itself is not axiom-free — it inherits `Init.Prelude`'s axiom table
(`sorryAx`, `Classical.choice`, `Quot.sound`, …) — but none of those appear
in the theorem's dependency chain, which is what the axiom checks test. All
of this is inside the kernel-checked environment (`doCheck := true` on every
declaration), so the standard kernel genuinely verifies each step.

## The honest boundary

* `lake comparator --paranoid` **rejects** this solution (exit 1): the
  con-leche and con-ron kernels diagnose it directly ("direct sum: large
  eliminator with a non-propositional field outside the indices [at inductive
  Exploit.P]"), nanoda rejects, and lean4lean errors. The default Lean kernel
  and leanchecker accept it — this project sits exactly on that line.
* The challenge is **self-referential**: challenge and solution are the same
  module, and the "trusted" challenge itself carries the exploit. Against the
  independent, honest challenge tested earlier (a normal `Init`-based module
  stating `1 + 1 = 3` with `sorry`), `lake comparator` rejects on the
  constant-comparison guard ("Const does not match between challenge and
  target 'autoParam'"): the dishonest root `autoParam` cannot coexist with
  the honest one, and we found no construction that passes that guard while
  keeping the challenge independent. What this project changes is the
  invocation — no flags — not that trust boundary.

## Files

* `ExploitKit.lean` — builder library (raw kernel `Declaration` API).
* `RichEnv.lean` — assembles + kernel-checks the padded environment, installs
  it as the module env; also writes `rich.olean` (a standalone copy).
* `Challenge.lean` — the prelude challenge module.
* `lakefile.lean`, `lean-toolchain` (`leanprover/lean4:v4.35.0`),
  `comparator.json` (challenge/solution module = `Challenge`,
  `theorem_names = ["one_add_one_eq_three"]`, `permitted_axioms = []`).
* `nanoda_*.json` — nanoda checker configs used by `--paranoid` runs
  (`con-leche` and `con-ron` run with their own defaults; no config files
  needed).
* `rich.export` — a pre-built `leanexport` NDJSON of the padded environment,
  for the alternative flag route:
  `lake comparator --challenge-from-export=rich.export --solution-from-export=rich.export`
  (also exits 0 with the standard kernel).
