import GaussianRiesz.ToL1
open MeasureTheory
theorem L2IntoL1 {n : ℕ} (v : Lp ℝ 2 (GaussMeasure n)) : ‖ToL1 v‖ ≤ ‖v‖ := by
  unfold ToL1
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable v))
