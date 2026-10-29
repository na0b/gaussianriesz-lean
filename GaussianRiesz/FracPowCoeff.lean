module

public import GaussianRiesz.MultiIndexSum

@[expose] public section
noncomputable def FracPowCoeff {n : ℕ} (s : ℝ) (c : (Fin n → ℕ) → ℝ) : (Fin n → ℕ) → ℝ :=
  fun α => if α = 0 then 0 else (MultiIndexSum α : ℝ) ^ s * c α
