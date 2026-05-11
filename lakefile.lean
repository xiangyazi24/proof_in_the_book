import Lake
open Lake DSL

package "proof_in_the_book" where

require Mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib ProofsInTheBook where
  srcDir := "."
