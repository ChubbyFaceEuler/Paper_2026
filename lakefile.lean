import Lake
open Lake DSL

package ZHY

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib ZHY where
  srcDir := "lean"
  roots := #[`ZHY_Core, `ZHY_Isserlis, `ZHY_BLUE, `ZHY_Theorem2, `ZHY_Opt]
