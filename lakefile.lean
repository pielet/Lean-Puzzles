import Lake
open Lake DSL

package "LeanPuzzles" where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require autograder from git "https://github.com/rkthomps/lean4-autograder-main" @ "master"
