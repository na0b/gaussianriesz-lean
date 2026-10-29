module

public import GaussianRiesz.GaussIsProb

@[expose] public section
open MeasureTheory
noncomputable def ComplexToL1 {n : ℕ} (v : Lp ℂ 2 (GaussMeasure n)) :
    Lp ℂ 1 (GaussMeasure n) :=
  MemLp.toLp (v : EuclideanSpace ℝ (Fin n) → ℂ) ((Lp.memLp v).mono_exponent (by norm_num))
