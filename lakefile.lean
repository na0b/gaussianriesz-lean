import Lake
open Lake DSL

package «gaussianriesz» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «GaussianRiesz» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0-rc2"
