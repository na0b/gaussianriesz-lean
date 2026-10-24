import GaussianRiesz.Energy
open MeasureTheory
noncomputable def EnergyBil {n : ℕ} (v w : Lp ℝ 2 (GaussMeasure n)) : ℝ :=
  ∑' α : {α : Fin n → ℕ // α ≠ 0},
    (MultiIndexSum (α : Fin n → ℕ) : ℝ) ^ ((1 : ℝ) / 2)
      * ((HermiteBasis n).repr v (α : Fin n → ℕ)) * ((HermiteBasis n).repr w (α : Fin n → ℕ))
