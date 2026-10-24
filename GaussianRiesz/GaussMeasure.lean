import GaussianRiesz.Preamble
open MeasureTheory
noncomputable def GaussMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity
    (fun x => ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)))
