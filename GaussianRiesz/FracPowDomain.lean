module

public import GaussianRiesz.FracPowCoeff
public import GaussianRiesz.HermiteBasis

@[expose] public section
open MeasureTheory
def FracPowDomain {n : ℕ} (s : ℝ) : Set (Lp ℝ 2 (GaussMeasure n)) :=
  {v | Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2}
