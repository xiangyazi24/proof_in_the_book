import Lake
open Lake DSL

package "proof_in_the_book" where
  version := "0.1.0"

-- Add Mathlib dependency when you are ready to build.
-- require Mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib ProofsInTheBook where
  srcDir := "."
