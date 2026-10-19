import Lake
open Lake DSL

package registry_viridis_canon_acc where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
