import Lake
open Lake DSL

package registry_aks where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- No standalone Mathlib dependency needed — spec imports AKS modules
-- which transitively bring in Mathlib. The spec is copied into the
-- impl repo during build_copy, so AKS modules are available.

@[default_target]
lean_lib «Registry» where
  srcDir := "."
