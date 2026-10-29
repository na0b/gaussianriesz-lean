module

public import GaussianRiesz.CoordinateEndpointBound
public import GaussianRiesz.SpectralNormalizationBound

@[expose] public section
open MeasureTheory
set_option linter.unusedVariables false
theorem UnnormalizedMeasureInvariance {n : ℕ}
    (T : Lp ℝ 1 (GaussMeasure n) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hext : ∀ v : Lp ℝ 2 (GaussMeasure n),
      T (ToL1 v) = (RieszTransform v : EuclideanSpace ℝ (Fin n)
        →ₘ[GaussMeasure n] EuclideanSpace ℝ (Fin n)))
    (hT : ∀ (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ), 0 < t →
      ENNReal.ofReal t * GaussMeasure n {x | t < ‖T f x‖} ≤ ENNReal.ofReal (2 * ‖f‖))
    (c : ℝ) (hc : 0 < c) (f : Lp ℝ 1 (GaussMeasure n)) (t : ℝ) (ht : 0 < t) :
    (∀ j : Fin n,
        ENNReal.ofReal t * (ENNReal.ofReal c • GaussMeasure n) {x | t < |T f x j|}
          ≤ ENNReal.ofReal (2 * ∫ x, |(f : EuclideanSpace ℝ (Fin n) → ℝ) x|
              ∂(ENNReal.ofReal c • GaussMeasure n)))
      ∧ ENNReal.ofReal t * (ENNReal.ofReal c • GaussMeasure n)
            {x | t < ‖((-Real.sqrt 2) • T) f x‖}
          ≤ ENNReal.ofReal (2 * Real.sqrt 2 * ∫ x,
              |(f : EuclideanSpace ℝ (Fin n) → ℝ) x|
                ∂(ENNReal.ofReal c • GaussMeasure n)) := by
  have hnorm : ‖f‖ = ∫ x, |(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := by
    rw [L1.norm_eq_integral_norm]
    simp [Real.norm_eq_abs]
  have hint : ∫ x, |(f : EuclideanSpace ℝ (Fin n) → ℝ) x|
        ∂(ENNReal.ofReal c • GaussMeasure n)
      = c * ∫ x, |(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ∂(GaussMeasure n) := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  constructor
  · intro j
    rw [Measure.smul_apply, smul_eq_mul, hint, ← hnorm, ← mul_assoc,
      mul_comm (ENNReal.ofReal t), mul_assoc]
    have hrhs : ENNReal.ofReal (2 * (c * ‖f‖))
        = ENNReal.ofReal c * ENNReal.ofReal (2 * ‖f‖) := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    rw [hrhs]
    gcongr
    exact CoordinateEndpointBound T hext hT f j t ht
  · rw [Measure.smul_apply, smul_eq_mul, hint, ← hnorm, ← mul_assoc,
      mul_comm (ENNReal.ofReal t), mul_assoc]
    have hrhs : ENNReal.ofReal (2 * Real.sqrt 2 * (c * ‖f‖))
        = ENNReal.ofReal c * ENNReal.ofReal (2 * Real.sqrt 2 * ‖f‖) := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    rw [hrhs]
    gcongr
    exact SpectralNormalizationBound T hext hT f t ht
