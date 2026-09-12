import Lake

open Lake DSL

package bklpsConjecture where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib BKLPS where
  globs := #[.one `BKLPS, .submodules `Proof]
