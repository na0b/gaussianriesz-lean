module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory
noncomputable def GaussRieszKernel {n : ℕ} (j : Fin n)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) *
    ∫ r in Set.Ioo (0 : ℝ) 1,
      (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))
