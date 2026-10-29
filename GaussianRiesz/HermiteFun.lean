module

public import GaussianRiesz.Hermite1
public import GaussianRiesz.MultiIndexSum
public import GaussianRiesz.GaussMeasure

@[expose] public section
noncomputable def HermiteFun {n : ℕ} (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ j, Hermite1 (α j) (x j)
