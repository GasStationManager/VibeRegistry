import Lake
open Lake DSL

package registry_artificial_theorems where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
