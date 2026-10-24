import GaussianRiesz.Preamble
def MultiIndexSum {n : ℕ} (α : Fin n → ℕ) : ℕ :=
  ∑ j, α j
