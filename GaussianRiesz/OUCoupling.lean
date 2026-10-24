import GaussianRiesz.GaussIsProb
open MeasureTheory
noncomputable def OUCoupling (n : ℕ) (s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  ((GaussMeasure n).prod (GaussMeasure n)).map
    (fun p => (p.1, Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2))
