import Lake
open System Lake DSL

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"main"

package «marktoberdorf2026» where
  version := v!"0.1.0"

lean_lib Lectures where
  globs := #[.submodules `Lectures]

@[default_target] lean_exe «marktoberdorf2026» where root := `Main
