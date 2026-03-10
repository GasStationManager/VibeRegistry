import Lake
open Lake DSL

package registry_aks where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
