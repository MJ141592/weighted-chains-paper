import Lake

open Lake DSL

require «weighted-chains» from ".."
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @
    "c3b8a93c5b97ff26f3ae23c5d0d06411ae416b42"
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @
    "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957"

package WeightedChainsBlueprint where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩
  ]

@[default_target]
lean_lib WeightedChainsBlueprint where
