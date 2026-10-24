import GaussianRiesz.SobolevW12
import GaussianRiesz.GaussWeakGradUnique
open MeasureTheory
open scoped Classical in
noncomputable def GaussD {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
  if h : v ∈ SobolevW12 n then h.choose else 0
