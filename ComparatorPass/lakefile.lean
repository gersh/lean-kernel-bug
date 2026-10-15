import Lake
open Lake DSL

package «comparatorpass»

-- ExploitKit: raw-API builder library for the kernel soundness PoC (PoC namespace)
-- RichEnv:    assembles + kernel-checks the padded environment and installs it
--             as the module environment (theorem + full comparator bundle)
-- Challenge:  prelude module that imports RichEnv; the challenge/solution
@[default_target]
lean_lib «Exploit» {
  roots := #[`ExploitKit, `RichEnv, `Challenge]
}
