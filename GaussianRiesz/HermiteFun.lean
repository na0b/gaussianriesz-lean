import GaussianRiesz.Hermite1
import GaussianRiesz.MultiIndexSum
import GaussianRiesz.GaussMeasure
noncomputable def HermiteFun {n : ℕ} (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ j, Hermite1 (α j) (x j)
