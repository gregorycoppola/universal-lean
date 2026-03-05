import Lake
open Lake DSL

package «universal-lean» where
  name := "universal-lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «UniversalLean» where
  roots := #[`UniversalLean]