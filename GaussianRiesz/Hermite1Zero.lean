module

public import GaussianRiesz.Hermite1

@[expose] public section
theorem Hermite1Zero : ∀ x : ℝ, Hermite1 0 x = 1 := by
  intro x
  simp [Hermite1, Polynomial.hermite_zero]
