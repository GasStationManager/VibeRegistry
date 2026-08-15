import Lake
open Lake DSL

package registry_degiorgi where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «DeGiorgi» from git
  "https://github.com/scottnarmstrong/DeGiorgi" @ "4c1b3077d3782b24065184df4ba59501b2e56fc7"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
