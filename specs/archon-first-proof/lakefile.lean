import Lake
open Lake DSL

package registry_archon_first_proof where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
