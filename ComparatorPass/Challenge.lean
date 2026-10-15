prelude
import RichEnv

/-!
# The challenge: `1 + 1 = 3`, kernel-checked with zero axioms

This module adds no declarations of its own. Importing `RichEnv` installs that
module's kernel-checked environment — built with `doCheck := true` on every
declaration — as this module's environment. That environment contains:

* `one_add_one_eq_three : 1 + 1 = 3`, verified by Lean's own kernel;
* the dishonest root `autoParam` and the `Exploit.*` machinery it enables
  (a proof of `False` with zero axioms, used ex falso);
* the full comparator fixed-constant bundle (the `String.mk` / `eagerReduce` /
  `Nat` binop pads).

`lake comparator` builds this module as both challenge and solution, exports
it, and hands it to Lean's default kernel — which accepts it.
-/
