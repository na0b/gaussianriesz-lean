module

public import GaussianRiesz.Preamble

@[expose] public section
def MultiIndexSum {n : ℕ} (α : Fin n → ℕ) : ℕ :=
  ∑ j, α j
