import ExploitKit
open Lean Elab Command

/-!
# 1 + 1 = 3, from the kernel soundness bug in `PoC.lean`

The bug (see `ExploitKit.lean` / `PoC.lean`): a crafted inductive
`Exploit.P (p : Type) : Prop` with parameter binder domain
`autoParam Prop Type` is *granted large elimination* by the Lean kernel
(`elim_only_at_universe_zero` in `src/kernel/inductive.cpp` treats the
parameter as a proof because it consumes the annotation syntactically).
`Exploit.f : Exploit.P Bool → Bool` then recovers the payload, proof
irrelevance equates `P.mk Bool true` and `P.mk Bool false`, and `Eq.rec`
transports `True.intro` into `False`. `PoC.lean` builds the environment with
`doCheck := true`, so the kernel itself checks every declaration — including
`Exploit.exploit : False` and `one_add_one_eq_three : 1 + 1 = 3` — with zero
axioms, and writes that exact environment as `exploit.olean` (verified by
`Verify.lean`).

Importing `exploit.olean` next to `Init` is impossible (its root-level
dishonest `autoParam` clashes with `Init.Tactics`'s), so this file re-presents
the theorem in ordinary surface syntax, transplanting the declarations at
elaboration time — see the comment above `run_cmd` for the trust boundary. -/

/- The `1 + 1 = 3` theorem in ordinary surface syntax, in a normal (full-`Init`)
Lean file. This file's presentation is trusted, not re-verified: the `Exploit.*`
declarations are re-added with checking disabled (`doCheck := false`) — the same
trust as importing a module — with the annotation constant renamed to
`Exploit.autoParam` (Init's root `autoParam` has a different universe arity,
and constant applications are arity-checked even on unchecked adds). Note that
re-adding the inductive regenerates `Exploit.P.rec` as the *honest* recursor in
this environment; nothing in this file's proof term depends on it. The
authoritative kernel-checked artifacts are `PoC.lean` (builds everything with
`doCheck := true` — the kernel itself accepts `Exploit.exploit : False` and
`one_add_one_eq_three : 1 + 1 = 3`), the `exploit.olean` it writes (that exact
checked environment), and `Verify.lean` (imports it and re-checks the axioms). -/
run_cmd do
  let mut env ← getEnv
  -- `Exploit.autoParam` is an ordinary function definition; add it checked.
  match env.addDeclCore 1000000 10000 (PoC.autoParamDeclAs `Exploit.autoParam)
      (cancelTk? := none) (doCheck := true) with
  | .ok env' => env := env'
  | .error e => throwError e.toMessageData {}
  for d in PoC.exploitDeclsCore `Exploit.autoParam do
    match env.addDeclCore 1000000 10000 d (cancelTk? := none) (doCheck := false) with
    | .ok env' => env := env'
    | .error e => throwError e.toMessageData {}
  modifyEnv fun _ => env

theorem one_add_one_eq_three : 1 + 1 = 3 := Exploit.exploit.elim

#check one_add_one_eq_three
#print axioms one_add_one_eq_three

