import Lake
open Lake DSL

package registry_lean_dirac_c19 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
