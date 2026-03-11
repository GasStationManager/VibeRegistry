import Lake
open Lake DSL

package registry_aks where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Spec imports AKS impl modules (available after copy into impl repo).
-- No standalone Mathlib dependency needed.

@[default_target]
lean_lib «Registry» where
  srcDir := "."
