prelude
import exploit

/-! Verification of the shipped `exploit.olean` (prelude-mode import; this
module has no root `autoParam` clash because `prelude` mode skips `Init`).
The olean is the exact kernel-checked environment built by `PoC.lean` with
`doCheck := true` — every declaration, including the theorem below, was
checked by the kernel. -/

-- The kernel-checked contradiction.
#check Exploit.exploit
#print axioms Exploit.exploit

-- The kernel-checked theorem. (In `prelude` mode there is no `+`/`=` notation,
-- so the statement displays in full application form; `OnePlusOne.lean` shows
-- it in ordinary surface syntax.)
#check one_add_one_eq_three
#print axioms one_add_one_eq_three

-- The recursor the kernel generated for the crafted inductive: a `Prop`
-- inductive eliminating into `Sort u` (large elimination).
#check Exploit.P.rec

#check Exploit.P
#check Exploit.f
#check Exploit.g
