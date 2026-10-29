module

public import GaussianRiesz.Preamble

@[expose] public section
open MeasureTheory
noncomputable def GaussMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity
    (fun x => ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)))
