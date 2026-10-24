import GaussianRiesz.Energy
import GaussianRiesz.Hermite1Zero
open MeasureTheory
open scoped Classical in
noncomputable def OUSemigroup {n : ℕ} (s : ℝ) (v : Lp ℝ 2 (GaussMeasure n)) :
    Lp ℝ 2 (GaussMeasure n) :=
  if h : Memℓp (fun α => Real.exp (-s * MultiIndexSum α) * (HermiteBasis n).repr v α) 2
    then (HermiteBasis n).repr.symm ⟨_, h⟩ else 0
