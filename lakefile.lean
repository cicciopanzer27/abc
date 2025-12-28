import Lake
open Lake DSL

package «borel-iut» where
  version := "0.1.0"
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4" "master"
  }]

@[default_target]
lean_lib «BorelIUT» where
  roots := #[`BorelIUT]
