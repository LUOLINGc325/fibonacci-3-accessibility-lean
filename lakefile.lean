import Lake
open Lake DSL

package fib3_access

@[default_target]
lean_lib FibAccess

/-- The three endpoint theorems (`spec/STATEMENT.lean`). -/
@[default_target]
lean_lib Statement where
  srcDir := "spec"
  roots := #[`STATEMENT]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
