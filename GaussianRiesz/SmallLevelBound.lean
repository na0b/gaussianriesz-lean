import GaussianRiesz.GaussIsProb
open MeasureTheory
-- binder retained for statement fidelity to the paper; intentionally unused in the proof
set_option linter.unusedVariables false
theorem SmallLevelBound {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (t M : ℝ) (ht : 0 < t) (htM : t ≤ M) :
    ENNReal.ofReal t * GaussMeasure n {x | t < ‖G x‖} ≤ ENNReal.ofReal M := by
  calc ENNReal.ofReal t * GaussMeasure n {x | t < ‖G x‖}
      ≤ ENNReal.ofReal t * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal t := by rw [mul_one]
    _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal htM
