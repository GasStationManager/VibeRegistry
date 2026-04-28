import Lake
open Lake DSL

package registry_lean_zip where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- For local development only. In the VibeRegistry verification pipeline the
-- Registry/ tree is overlaid into the impl repo via build_copy.sh and this
-- lakefile is not used.
require «lean-zip» from git
  "https://github.com/kim-em/lean-zip" @ "e76f0813faa2893f09b83d027e52754041febc35"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
