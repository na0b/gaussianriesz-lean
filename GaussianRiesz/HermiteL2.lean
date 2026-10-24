import GaussianRiesz.HermiteFunMemLp
open MeasureTheory
noncomputable def HermiteL2 {n : ℕ} (α : Fin n → ℕ) : Lp ℝ 2 (GaussMeasure n) :=
  MemLp.toLp (HermiteFun α) (HermiteFunMemLp α)
