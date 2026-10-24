import GaussianRiesz.HermiteBasis
import GaussianRiesz.MultiIndexSum
import GaussianRiesz.FracPowDomain
open MeasureTheory
noncomputable def Energy {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) : ENNReal :=
  ∑' α : {α : Fin n → ℕ // α ≠ 0},
    ENNReal.ofReal ((MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
      * ((HermiteBasis n).repr v (α : Fin n → ℕ)) ^ 2)
