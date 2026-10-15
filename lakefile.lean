import Lake
open Lake DSL

package gbkernelexploit

@[default_target]
lean_lib GBKernelExploit where
  roots := #[`ExploitKit, `PoC, `one_plus_one]
