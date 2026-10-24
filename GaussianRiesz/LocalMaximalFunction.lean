import GaussianRiesz.Preamble
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Metric
open scoped ENNReal
noncomputable def LocalMaximalFunction {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ ρ ∈ Set.Ioc (0 : ℝ) 2,
    (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖w y‖ₑ
