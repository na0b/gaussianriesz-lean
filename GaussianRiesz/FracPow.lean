module

public import GaussianRiesz.FracPowDomain
public import GaussianRiesz.HermiteFunOU

@[expose] public section
open MeasureTheory
open scoped Classical in
noncomputable def FracPow {n : ℕ} (s : ℝ) (v : Lp ℝ 2 (GaussMeasure n)) :
    Lp ℝ 2 (GaussMeasure n) :=
  if h : Memℓp (FracPowCoeff s (fun α => (HermiteBasis n).repr v α)) 2
    then (HermiteBasis n).repr.symm ⟨_, h⟩ else 0
