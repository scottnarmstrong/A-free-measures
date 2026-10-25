import Lake

open Lake DSL

package «a_free_measures» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

/-- The coordinate model of `ℝ^d` and the weak type (1,1) estimate for the gradient of the
Newtonian potential, from EllipticRegularityLean. -/
require elliptic_regularity from git
  "https://github.com/scottnarmstrong/EllipticRegularityLean.git" @
    "1e29da02bcc6e3c2359a5b8e0559e76d02ec4002"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- The library: the definitions, the infrastructure and the proofs. -/
@[default_target]
lean_lib «AFree» where
  leanOptions := projectLeanOptions

/-- The 25 main theorems, one per file, each proved by `AFree.<Name>Proof.result`. -/
@[default_target]
lean_lib «AFreeStatements» where
  leanOptions := projectLeanOptions

/-- The comparator challenge: the 25 statements with every definition they use, from Mathlib only
(`Challenge.lean`), their proofs from this library (`Solution.lean`) and the axiom audit. Check with
`scripts/verify_comparator.sh`. -/
lean_lib «AFreeChallenges» where
  globs := #[.submodules `AFreeChallenges]
  leanOptions := projectLeanOptions
