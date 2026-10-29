module

public import GaussianRiesz.Preamble
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section
open MeasureTheory Metric
open scoped ENNReal
noncomputable def LocalMaximalFunction {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ ρ ∈ Set.Ioc (0 : ℝ) 2,
    (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖w y‖ₑ
