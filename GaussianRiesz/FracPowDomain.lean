import GaussianRiesz.FracPowCoeff
import GaussianRiesz.HermiteBasis
open MeasureTheory
def FracPowDomain {n : ℕ} (s : ℝ) : Set (Lp ℝ 2 (GaussMeasure n)) :=
  {v | Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2}
