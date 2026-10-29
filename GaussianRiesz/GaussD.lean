module

public import GaussianRiesz.SobolevW12
public import GaussianRiesz.GaussWeakGradUnique

@[expose] public section
open MeasureTheory
open scoped Classical in
noncomputable def GaussD {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (GaussMeasure n) :=
  if h : v ∈ SobolevW12 n then h.choose else 0
