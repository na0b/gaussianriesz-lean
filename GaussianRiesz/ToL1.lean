module

public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
noncomputable def ToL1 {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) : Lp ℝ 1 (GaussMeasure n) :=
  MemLp.toLp (v : EuclideanSpace ℝ (Fin n) → ℝ) ((Lp.memLp v).mono_exponent (by norm_num))
